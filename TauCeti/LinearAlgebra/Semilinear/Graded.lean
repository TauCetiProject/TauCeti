/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Semilinear.Filtration
public import TauCeti.RingTheory.QuotSMulTop.Graded

/-!
# Semilinear maps on scalar-power graded pieces

A semilinear endomorphism fixing a scalar `a` acts on the successive quotients
`a^i M / a^{i+1} M`. The surjection from `M / aM` onto each piece intertwines the induced
endomorphisms. If the filtration terminates, bijectivity can be checked on its graded pieces.
-/

public section

namespace LinearMap

open Function TauCeti
open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {σ : A →+* A}
  {f : M →ₛₗ[σ] M} {a : A}

local notation "P" => (fun i : ℕ ↦ a ^ i • (⊤ : Submodule A M))
local notation "Q" => (a • (⊤ : Submodule A M))

/-- The map induced by a semilinear endomorphism on `a^i M / a^{i+1} M` for a fixed scalar `a`. -/
def smulPowGraded (f : M →ₛₗ[σ] M) (ha : σ a = a) (i : ℕ) :
    (P i ⧸ (P (i + 1)).comap (P i).subtype) →ₛₗ[σ] (P i ⧸ (P (i + 1)).comap (P i).subtype) :=
  f.subquotientMap (P i) (P (i + 1)) (f.mapsTo_pow_smul_top_of_fixed ha i)
    (f.mapsTo_pow_smul_top_of_fixed ha (i + 1))

/-- The graded map is the subquotient map of two successive scalar powers. -/
theorem smulPowGraded_eq_subquotientMap (f : M →ₛₗ[σ] M) (ha : σ a = a) (i : ℕ) :
    f.smulPowGraded ha i =
      f.subquotientMap (P i) (P (i + 1)) (f.mapsTo_pow_smul_top_of_fixed ha i)
        (f.mapsTo_pow_smul_top_of_fixed ha (i + 1)) :=
  (rfl)

/-- The map on a graded piece sends the class of a vector to the class of its image. -/
@[simp]
theorem smulPowGraded_mk (f : M →ₛₗ[σ] M) (ha : σ a = a) (i : ℕ) (x : P i) :
    f.smulPowGraded ha i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f x, f.mapsTo_pow_smul_top_of_fixed ha i x.property⟩ := by
  rw [smulPowGraded_eq_subquotientMap]
  exact (subquotientMap_mk (P i) (P (i + 1)) _ _ x).trans
    (congrArg Submodule.Quotient.mk (restrict_apply (f.mapsTo_pow_smul_top_of_fixed ha i) x))

/-- Multiplication by `a^i` intertwines the induced maps on `M / aM` and `a^i M / a^{i+1} M`. -/
theorem smulPowQuotientMap_semiconj (f : M →ₛₗ[σ] M) (ha : σ a = a) (i : ℕ) :
    Semiconj (smulPowQuotientMap a i) (Submodule.mapQ Q Q f (f.mapsTo_smul_top_of_fixed ha))
      (f.smulPowGraded ha i) := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Q z
  calc
    _ = smulPowQuotientMap a i (Submodule.Quotient.mk (f x)) :=
      congrArg (smulPowQuotientMap a i) (Submodule.mapQ_apply Q Q f x)
    _ = _ := by
      simp only [smulPowQuotientMap_mk, smulPowGraded_mk]
      apply congrArg (Submodule.Quotient.mk (p := (P (i + 1)).comap (P i).subtype))
      exact Subtype.ext (by simp only [map_smulₛₗ, map_pow, ha])

/-- A bijective endomorphism is bijective on each graded piece for a fixed scalar. -/
theorem bijective_smulPowGraded (hf : Bijective f) (ha : σ a = a) (i : ℕ) :
    Bijective (f.smulPowGraded ha i) := by
  rw [smulPowGraded]
  apply bijective_subquotientMap _ _ _ _ (f.surjOn_smul_top_of_fixed hf.2 (by simp [ha]))
  intro x _ hx
  obtain ⟨y, hy, hyf⟩ := f.surjOn_smul_top_of_fixed hf.2 (a := a ^ (i + 1)) (by simp [ha]) hx
  exact hf.1 hyf ▸ hy

/-- Bijectivity on all graded pieces of a finite fixed-scalar filtration implies bijectivity
on the module. -/
theorem bijective_of_smulPowGraded (ha : σ a = a) {n : ℕ} (hbot : P n = ⊥)
    (h : ∀ i < n, Bijective (f.smulPowGraded ha i)) : Bijective f := by
  have h₀ := bijective_restrict_of_filtration P (f.mapsTo_pow_smul_top_of_fixed ha)
    (Submodule.antitone_pow_smul_top a) hbot
    (fun i hi ↦ by simpa only [smulPowGraded_eq_subquotientMap] using h i hi)
  have htop : P 0 = ⊤ := by simp
  have he : Bijective (P 0).subtype := htop.symm ▸ Submodule.topEquiv.bijective
  exact (Bijective.of_comp_iff f he).mp (he.comp h₀)

end LinearMap
