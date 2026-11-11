/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.GenusZero
public import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct

/-!
# The Picard group of the projective line over a field

Degree identifies `Pic(ℙ¹_k)` with `ℤ`, and its inverse sends `n` to the class of `𝒪(n)`.
Consequently every line bundle on `ℙ¹_k` is isomorphic to exactly one twisting sheaf.
In particular, a rational point defines the class of `𝒪(1)`, not the trivial class, and
the abstract degree-zero Picard group is trivial.

These are statements about isomorphism classes of line bundles on `ℙ¹_k`, not a
representability assertion for the relative Picard functor on arbitrary test schemes.
The ground field is arbitrary, including imperfect fields.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.17 and Chapter III,
  Theorem 5.1.
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

noncomputable section

variable (k : Type u) [Field k]

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
local notation "ℒ" => fun n : ℤ ↦
  (ObjectProperty.FullSubcategory.mk (Proj.twistingSheaf 𝒜 n) inferInstance :
    InvertibleSheaf (projectiveLine k))

local instance : IsNoetherian (projectiveLine k) :=
  isNoetherian_of_finiteType (projectiveLine k ↘ Spec (.of k))

local instance : Fact (∀ x : projectiveLine k, coheight x ≤ 1) :=
  ⟨Scheme.IsCurveOver.coheight_le_one (k := k)⟩

/-- Degree classifies line bundles on the projective line over any field. -/
private theorem eulerDegree_injective :
    Function.Injective (LineBundleClass.eulerDegree k :
      LineBundleClass (projectiveLine k) → ℤ) :=
  LineBundleClass.eulerDegree_injective_of_genus_eq_zero
    (Scheme.IsCurveOver.coheight_le_one (k := k))
    (bijective_baseRingToGlobalSections k).surjective (genus_eq_zero k)

/-- The degree of `𝒪(1)` on the projective line is one. -/
private theorem eulerDegree_twistingSheaf_one : InvertibleSheaf.eulerDegree k (ℒ 1) = 1 := by
  have : Subsingleton (Scheme.Modules.Cohomology (Proj.twistingSheaf 𝒜 1) 1) :=
    (Pi.basisFun k (Fin 2)).subsingleton_cohomology_twistingSheaf_of_neg_card_lt
      (by norm_num) (by decide)
  have h₀ : Module.finrank k
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (projectiveLine k)).obj 0) = 1 :=
    (cohomologyZeroTrivialLinearEquiv k).finrank_eq.trans (Module.finrank_self k)
  simp only [InvertibleSheaf.eulerDegree_eq_finrank_sub,
    finrank_cohomology_zero_twistingSheaf, Module.finrank_zero_of_subsingleton, h₀]
  norm_num

/-- Every twisting sheaf `𝒪(n)` on the projective line has degree `n`, for `n : ℤ`. -/
@[simp]
theorem eulerDegree_twistingSheaf (n : ℤ) : InvertibleSheaf.eulerDegree k (ℒ n) = n := by
  have hclass := Proj.lineBundleClass_twistingSheaf_eq_zpow
    (fun i : ULift.{u} (Fin 2) ↦ coord k i.down) (fun i ↦ coord_mem k i.down)
    (by simpa only [iSup_ulift] using iSup_basicOpen_coord_eq_top k) n
  rw [← LineBundleClass.eulerDegree_mk, hclass,
    LineBundleClass.eulerDegree_zpow k,
    LineBundleClass.eulerDegree_mk, eulerDegree_twistingSheaf_one, mul_one]

/-- **`Pic(ℙ¹_k) ≃ ℤ`**, via degree; tensor product is written additively on the source.
The inverse sends an integer `n` to the class of the twisting sheaf `𝒪(n)`. -/
def picardDegreeEquiv : Additive (LineBundleClass (projectiveLine k)) ≃+ ℤ :=
  LineBundleClass.picardDegreeEquivOfGenusZero
    (bijective_baseRingToGlobalSections k).surjective (genus_eq_zero k)
    (LineBundleClass.mk (ℒ 1)) (by
      simpa only [LineBundleClass.eulerDegree_mk] using eulerDegree_twistingSheaf_one k)

/-- The Picard-group identification with `ℤ` evaluates to the Euler-characteristic degree. -/
@[simp]
lemma picardDegreeEquiv_apply (a : Additive (LineBundleClass (projectiveLine k))) :
    picardDegreeEquiv k a = LineBundleClass.eulerDegree k a.toMul :=
  LineBundleClass.picardDegreeEquivOfGenusZero_apply _ _ _ _ a

/-- The inverse Picard-group identification sends `n` to `[𝒪(n)]`. -/
@[simp]
lemma picardDegreeEquiv_symm_apply (n : ℤ) :
    (picardDegreeEquiv k).symm n = Additive.ofMul (LineBundleClass.mk (ℒ n)) := by
  apply (picardDegreeEquiv k).injective
  simp

/-- A line bundle on the projective line is isomorphic to `𝒪(n)` exactly when its degree is `n`.
Thus the integer in the twisting-sheaf classification is unique. -/
@[simp]
theorem nonempty_iso_twistingSheaf_iff (L : InvertibleSheaf (projectiveLine k)) (n : ℤ) :
    Nonempty (L.obj ≅ Proj.twistingSheaf 𝒜 n) ↔ L.eulerDegree k = n := by
  rw [← LineBundleClass.mk_eq_mk_iff (L := L) (K := ℒ n)]
  exact (eulerDegree_injective k).eq_iff.symm.trans (by simp)

/-- The line-bundle class of every rational point of the projective line is `[𝒪(1)]`. -/
theorem toLineBundleClass_ofPoint_eq_twistingSheaf_one
    (x : CodimensionOnePoint (projectiveLine k))
    (hx : (projectiveLine k ↘ Spec (.of k)).residueDegree x = 1) :
    SchemeWeilDivisor.toLineBundleClass
        (Scheme.IsCurveOver.coheight_le_one (k := k)) (WeilDivisor.ofPoint x) =
      LineBundleClass.mk (ℒ 1) := by
  apply eulerDegree_injective k
  simp [hx]

/-- The abstract degree-zero Picard group of the projective line is trivial. -/
@[simp]
theorem picZero_eq_bot : LineBundleClass.picZero k (projectiveLine k) = ⊥ :=
  LineBundleClass.picZero_eq_bot_of_genus_eq_zero
    (bijective_baseRingToGlobalSections k).surjective (genus_eq_zero k)

end

end TauCeti.AlgebraicGeometry.projectiveLine
