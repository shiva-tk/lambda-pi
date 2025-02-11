module LambdaArrowSpec where

import LambdaArrow

import Test.Hspec ( hspec, describe, it, shouldBe, SpecWith )

lambdaArrowSpec :: IO ()
lambdaArrowSpec = do
  hspec $ describe "src/LambdaArrow.hs" $ do

    it "Free Var" $
      readInferable "  xyz " `shouldBe` Right (Free (Global "xyz"), [])

    it "Simple Annotation" $
      readInferable "(x) :: a -> a" `shouldBe` Right (Ann (Inf $ Free $ Global "x") (TFun (TFree $ Global "a") (TFree $ Global "a")), [])

    it "Annotation" $
      readInferable "(\\ x.x) :: a -> a" `shouldBe` Right (Ann (Lam $ Inf $ Bound 0) (TFun (TFree $ Global "a") (TFree $ Global "a")), ["x"])

    it "Multiple Bound Vars" $
      readInferable "(\\ x. \\ y z w .   y) :: a -> a" `shouldBe`
      Right (Ann (Lam $ Lam $ Lam $ Lam $ Inf $ Bound 2) (TFun (TFree $ Global "a") (TFree $ Global "a")), ["x", "y", "z", "w"])

    it "Application" $
      readInferable "((\\ x. \\ y z w .   y) :: a -> a) (x)" `shouldBe`
      Right ((Ann (Lam $ Lam $ Lam $ Lam $ Inf $ Bound 2) (TFun (TFree $ Global "a") (TFree $ Global "a"))) :@: (Inf $ Free (Global "x")), ["x", "y", "z", "w"])
