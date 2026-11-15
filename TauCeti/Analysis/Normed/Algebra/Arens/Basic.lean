/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import TauCeti.Analysis.Normed.Module.Dual.Bilinear

/-!
# The two Arens products

The bidual of a nonunital normed algebra has two associative bounded products, obtained
by extending multiplication in opposite orders. We keep these as explicit bounded
bilinear maps `TauCeti.arensMul` and `TauCeti.arensMulRev`, rather than choosing a
multiplication instance on the bidual. Both extend the original multiplication and
agree whenever either argument belongs to the original algebra.

The first product is weak-star continuous in its first variable, and the second in
its second variable. On the canonical image of the original algebra they are also
weak-star continuous in the other variable. No completeness or identity is needed.

See H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.6.
-/

public noncomputable section

open NormedSpace ContinuousLinearMap

namespace TauCeti

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

-- Prefer the direct operator instances when elaborating the curried bidual products.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup ContinuousLinearMap.strongBidualNormedSpace

/-- The first Arens product, with evaluation order `F (a ↦ G (b ↦ f (a * b)))`. -/
def arensMul : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 A) :=
  (ContinuousLinearMap.mul 𝕜 A).arensExtension

/-- The second Arens product, with evaluation order `G (b ↦ F (a ↦ f (a * b)))`. -/
def arensMulRev : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 A) :=
  (ContinuousLinearMap.mul 𝕜 A).flip.arensExtension.flip

variable {𝕜 A}

/-- Evaluation of the first Arens product, expressed with bounded transposes. -/
@[simp]
theorem arensMul_apply (F G : StrongDual 𝕜 (StrongDual 𝕜 A)) (f : StrongDual 𝕜 A) :
    arensMul 𝕜 A F G f =
      F ((ContinuousLinearMap.mul 𝕜 A).bilinearTranspose.bilinearTranspose G f) := by
  exact (ContinuousLinearMap.mul 𝕜 A).arensExtension_apply F G f

/-- Evaluation of the second Arens product, expressed with bounded transposes. -/
@[simp]
theorem arensMulRev_apply (F G : StrongDual 𝕜 (StrongDual 𝕜 A)) (f : StrongDual 𝕜 A) :
    arensMulRev 𝕜 A F G f =
      G ((ContinuousLinearMap.mul 𝕜 A).flip.bilinearTranspose.bilinearTranspose F f) := by
  exact (ContinuousLinearMap.mul 𝕜 A).flip.arensExtension_apply G F f

/-- The first Arens product is submultiplicative. -/
theorem norm_arensMul_le (F G : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    ‖arensMul 𝕜 A F G‖ ≤ ‖F‖ * ‖G‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.mul 𝕜 A‖ * ‖F‖ * ‖G‖ :=
      norm_arensExtension_apply_le _ F G
    _ ≤ 1 * ‖F‖ * ‖G‖ := by gcongr; exact opNorm_mul_le 𝕜 A
    _ = _ := by rw [one_mul]

/-- The second Arens product is submultiplicative. -/
theorem norm_arensMulRev_le (F G : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    ‖arensMulRev 𝕜 A F G‖ ≤ ‖F‖ * ‖G‖ := by
  calc
    _ ≤ ‖(ContinuousLinearMap.mul 𝕜 A).flip‖ * ‖G‖ * ‖F‖ :=
      norm_arensExtension_apply_le _ G F
    _ ≤ 1 * ‖G‖ * ‖F‖ := by gcongr; rw [opNorm_flip]; exact opNorm_mul_le 𝕜 A
    _ = _ := by ring

/-- The first Arens product extends multiplication on the original algebra. -/
@[simp]
theorem arensMul_inclusionInDoubleDual (a b : A) :
    arensMul 𝕜 A (inclusionInDoubleDual 𝕜 A a) (inclusionInDoubleDual 𝕜 A b) =
      inclusionInDoubleDual 𝕜 A (a * b) := by
  exact (ContinuousLinearMap.mul 𝕜 A).arensExtension_inclusionInDoubleDual a b

/-- The second Arens product extends multiplication on the original algebra. -/
@[simp]
theorem arensMulRev_inclusionInDoubleDual (a b : A) :
    arensMulRev 𝕜 A (inclusionInDoubleDual 𝕜 A a) (inclusionInDoubleDual 𝕜 A b) =
      inclusionInDoubleDual 𝕜 A (a * b) := by
  exact (ContinuousLinearMap.mul 𝕜 A).flip.arensExtension_inclusionInDoubleDual b a

/-- The products agree when the first argument is in the original algebra. -/
theorem arensMul_inclusionInDoubleDual_left_eq_arensMulRev
    (a : A) (G : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMul 𝕜 A (inclusionInDoubleDual 𝕜 A a) G =
      arensMulRev 𝕜 A (inclusionInDoubleDual 𝕜 A a) G := by
  exact (ContinuousLinearMap.mul 𝕜 A).arensExtension_inclusionInDoubleDual_left_eq_flip a G

/-- The products agree when the second argument is in the original algebra. -/
theorem arensMul_inclusionInDoubleDual_right_eq_arensMulRev
    (F : StrongDual 𝕜 (StrongDual 𝕜 A)) (b : A) :
    arensMul 𝕜 A F (inclusionInDoubleDual 𝕜 A b) =
      arensMulRev 𝕜 A F (inclusionInDoubleDual 𝕜 A b) := by
  exact (ContinuousLinearMap.mul 𝕜 A).arensExtension_inclusionInDoubleDual_right_eq_flip F b

/-- Associativity of the first Arens product. -/
theorem arensMul_assoc (F G H : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMul 𝕜 A (arensMul 𝕜 A F G) H = arensMul 𝕜 A F (arensMul 𝕜 A G H) := by
  ext f
  simp only [arensMul_apply]
  congr 1
  ext a
  simp only [bilinearTranspose_apply, arensMul_apply]
  congr 1
  ext b
  simp only [bilinearTranspose_apply]
  congr 1
  ext c
  simp [mul_assoc]

/-- Associativity of the second Arens product. -/
theorem arensMulRev_assoc (F G H : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMulRev 𝕜 A (arensMulRev 𝕜 A F G) H =
      arensMulRev 𝕜 A F (arensMulRev 𝕜 A G H) := by
  ext f
  simp only [arensMulRev_apply]
  congr 1
  ext c
  simp only [bilinearTranspose_apply, arensMulRev_apply]
  congr 1
  ext b
  simp only [bilinearTranspose_apply]
  congr 1
  ext a
  simp [mul_assoc]

/-- Right multiplication for the first product is weak-star continuous. -/
theorem continuous_toWeakDual_arensMul_left (G : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    Continuous (fun F : WeakDual 𝕜 (StrongDual 𝕜 A) =>
      StrongDual.toWeakDual (arensMul 𝕜 A F.toStrongDual G)) :=
  (ContinuousLinearMap.mul 𝕜 A).continuous_toWeakDual_arensExtension_left G

/-- Left multiplication for the second product is weak-star continuous. -/
theorem continuous_toWeakDual_arensMulRev_right (F : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    Continuous (fun G : WeakDual 𝕜 (StrongDual 𝕜 A) =>
      StrongDual.toWeakDual (arensMulRev 𝕜 A F G.toStrongDual)) :=
  (ContinuousLinearMap.mul 𝕜 A).flip.continuous_toWeakDual_arensExtension_left F

/-- Left multiplication by an original algebra element is weak-star continuous for
the first product as well. -/
theorem continuous_toWeakDual_arensMul_inclusionInDoubleDual_right (a : A) :
    Continuous (fun G : WeakDual 𝕜 (StrongDual 𝕜 A) =>
      StrongDual.toWeakDual (arensMul 𝕜 A (inclusionInDoubleDual 𝕜 A a) G.toStrongDual)) :=
  (ContinuousLinearMap.mul 𝕜 A).continuous_toWeakDual_arensExtension_inclusionInDoubleDual_right a

/-- Right multiplication by an original algebra element is weak-star continuous for
the second product as well. -/
theorem continuous_toWeakDual_arensMulRev_inclusionInDoubleDual_left (b : A) :
    Continuous (fun F : WeakDual 𝕜 (StrongDual 𝕜 A) =>
      StrongDual.toWeakDual (arensMulRev 𝕜 A F.toStrongDual (inclusionInDoubleDual 𝕜 A b))) :=
  ContinuousLinearMap.continuous_toWeakDual_arensExtension_inclusionInDoubleDual_right
    (ContinuousLinearMap.mul 𝕜 A).flip b

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalSeminormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalSeminormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]

/-- The second adjoint of a bounded multiplicative linear map preserves the first
Arens product. Neither unitality nor a contractive norm bound is required. -/
theorem precomp_precomp_arensMul (T : A →L[𝕜] B)
    (hT : ∀ a b, T (a * b) = T a * T b) (F G : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    precomp 𝕜 (precomp 𝕜 T) (TauCeti.arensMul 𝕜 A F G) =
      TauCeti.arensMul 𝕜 B (precomp 𝕜 (precomp 𝕜 T) F) (precomp 𝕜 (precomp 𝕜 T) G) := by
  exact (mul 𝕜 A).precomp_precomp_arensExtension (mul 𝕜 B) T T T hT F G

/-- The second adjoint of a bounded multiplicative linear map preserves the second
Arens product. -/
theorem precomp_precomp_arensMulRev (T : A →L[𝕜] B)
    (hT : ∀ a b, T (a * b) = T a * T b) (F G : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    precomp 𝕜 (precomp 𝕜 T) (TauCeti.arensMulRev 𝕜 A F G) =
      TauCeti.arensMulRev 𝕜 B (precomp 𝕜 (precomp 𝕜 T) F) (precomp 𝕜 (precomp 𝕜 T) G) := by
  exact (mul 𝕜 A).flip.precomp_precomp_arensExtension (mul 𝕜 B).flip T T T
    (fun a b => hT b a) G F

end ContinuousLinearMap

namespace TauCeti

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [SeminormedRing A] [NormedAlgebra 𝕜 A]

/-- The image of the original identity is a left identity for the first Arens product. -/
@[simp]
theorem arensMul_one_left (F : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMul 𝕜 A (inclusionInDoubleDual 𝕜 A 1) F = F := by
  ext f
  simp only [arensMul_apply, dual_def, bilinearTranspose_apply]
  congr 1
  ext a
  simp

/-- The image of the original identity is a right identity for the first Arens product. -/
@[simp]
theorem arensMul_one_right (F : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMul 𝕜 A F (inclusionInDoubleDual 𝕜 A 1) = F := by
  ext f
  simp only [arensMul_apply]
  congr 1
  ext a
  simp

/-- The image of the original identity is a left identity for the second Arens product. -/
@[simp]
theorem arensMulRev_one_left (F : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMulRev 𝕜 A (inclusionInDoubleDual 𝕜 A 1) F = F := by
  rw [← arensMul_inclusionInDoubleDual_left_eq_arensMulRev, arensMul_one_left]

/-- The image of the original identity is a right identity for the second Arens product. -/
@[simp]
theorem arensMulRev_one_right (F : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    arensMulRev 𝕜 A F (inclusionInDoubleDual 𝕜 A 1) = F := by
  rw [← arensMul_inclusionInDoubleDual_right_eq_arensMulRev, arensMul_one_right]

end Unital

end TauCeti
