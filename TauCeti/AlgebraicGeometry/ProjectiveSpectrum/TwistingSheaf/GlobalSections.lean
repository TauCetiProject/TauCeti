/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# Global sections of the twisting sheaves on projective space

Let `M` be a free `R`-module with a basis indexed by a type `κ` with at least two elements, and let
`A = Sym M ≅ R[Xᵢ | i ∈ κ]`, graded by degree, so that `Proj A` is projective space over `R` with
the basis vectors as homogeneous coordinates. This file computes the global sections of the
twisting sheaves `𝒪(n)` on `Proj A`, over any commutative ring `R`:

* for `n ≥ 0`, the map `A_n → Γ(Proj A, 𝒪(n))`, `r ↦ r / 1`, is bijective, so the global
  sections of `𝒪(n)` are the forms of degree `n`;
* for `n < 0`, `𝒪(n)` has no nonzero global sections.

This is Hartshorne, Proposition II.5.13, the degreewise form of Theorem III.5.1(a). The
hypothesis that `κ` has two elements cannot be dropped: for a single coordinate, `Proj A` is
`Spec R` and every `𝒪(n)` is trivial, with global sections `R` also for `n < 0`.

On the standard open `D₊(Xᵢ)`, a global section `s` is a fraction `rᵢ / Xᵢ ^ kᵢ`
(`AlgebraicGeometry.Proj.twistingSheaf.exists_eq_const_basicOpen`). Since the coordinates are
nonzerodivisors in `A`, these fractions agreeing on the overlaps `D₊(Xᵢ Xⱼ)` amounts to
`Xⱼ ^ kⱼ * rᵢ = Xᵢ ^ kᵢ * rⱼ` in `A`. For two distinct coordinates `X₀ = Xᵢ` and `X₁ = Xⱼ` this
gives `X₀ ^ k₀ ∣ X₁ ^ k₁ * r₀`, hence `X₀ ^ k₀ ∣ r₀`
(`SymmetricAlgebra.ι_basis_pow_dvd_ι_basis_pow_mul_iff`). Writing `r₀ = X₀ ^ k₀ * q`, every `rᵢ` is
`Xᵢ ^ kᵢ * q`, so `s` is the function `q / 1` on the cover by the `D₊(Xᵢ)`. Comparing homogeneous
components, `q` is a form of degree `n` when `n ≥ 0`, and `q = 0` when `n < 0`.

## Main results

* `TauCeti.SymmetricAlgebra.bijective_toTwistingSheaf_top`: for `j : ℕ`, the map
  `A_j → Γ(Proj A, 𝒪(j))` is bijective.
* `TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivTwistingSheafTop`: the resulting additive
  isomorphism `A_j ≃+ Γ(Proj A, 𝒪(j))`.
* `TauCeti.SymmetricAlgebra.twistingSheaf_top_eq_zero_of_neg`: for `n < 0`, every global section
  of `𝒪(n)` vanishes.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition II.5.13 and
  Theorem III.5.1(a).
* [Stacks, Lemma 30.8.1 (01XS)](https://stacks.math.columbia.edu/tag/01XS)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open _root_.SymmetricAlgebra (ι isRegular_ι_basis ι_basis_pow_dvd_ι_basis_pow_mul_iff)

namespace TauCeti.SymmetricAlgebra

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M] {κ : Type*}

local notation "𝒜" => homogeneousSubmodule R M

/-- On the overlap `D₊(Xᵢ Xⱼ)`, two fractions `rᵢ / Xᵢ ^ kᵢ` and `rⱼ / Xⱼ ^ kⱼ` of a section agree
exactly when `Xⱼ ^ kⱼ * rᵢ = Xᵢ ^ kᵢ * rⱼ`: the coordinates are nonzerodivisors, so the
localization `A_{XᵢXⱼ}` does not identify more. -/
private theorem mul_eq_mul_of_restrict_eq (b : Module.Basis κ R M) {n : ℤ} {i j : κ}
    {kᵢ kⱼ jᵢ jⱼ : ℕ}
    (hᵢ : (jᵢ : ℤ) = (kᵢ * 1 : ℕ) + n) (hⱼ : (jⱼ : ℤ) = (kⱼ * 1 : ℕ) + n)
    {rᵢ rⱼ : _root_.SymmetricAlgebra R M} (hrᵢ : rᵢ ∈ 𝒜 jᵢ) (hrⱼ : rⱼ ∈ 𝒜 jⱼ)
    (hsᵢ : ι R M (b i) ^ kᵢ ∈ 𝒜 (kᵢ * 1)) (hsⱼ : ι R M (b j) ^ kⱼ ∈ 𝒜 (kⱼ * 1))
    (hUᵢ : Proj.basicOpen 𝒜 (ι R M (b i)) ≤ Proj.basicOpen 𝒜 (ι R M (b i) ^ kᵢ))
    (hUⱼ : Proj.basicOpen 𝒜 (ι R M (b j)) ≤ Proj.basicOpen 𝒜 (ι R M (b j) ^ kⱼ))
    (s : Γ(Proj.twistingSheaf 𝒜 n, ⊤))
    (eᵢ : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s =
      Proj.twistingSheaf.const hᵢ rᵢ _ hrᵢ hsᵢ _ hUᵢ)
    (eⱼ : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s =
      Proj.twistingSheaf.const hⱼ rⱼ _ hrⱼ hsⱼ _ hUⱼ) :
    ι R M (b j) ^ kⱼ * rᵢ = ι R M (b i) ^ kᵢ * rⱼ := by
  have hle := (Proj.basicOpen_mul 𝒜 (ι R M (b i)) (ι R M (b j))).le
  -- both sides are the restriction of `s` to the overlap: restricting a section keeps its values,
  -- which is `Proj.twistingSheaf.res_apply`, true by `rfl`
  have e : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE (hle.trans inf_le_left)).op
      ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s) =
      (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE (hle.trans inf_le_right)).op
        ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s) :=
    Proj.twistingSheaf.ext fun _ ↦ rfl
  rw [eᵢ, eⱼ, Proj.twistingSheaf.res_const, Proj.twistingSheaf.res_const,
    Proj.twistingSheaf.const_eq_const_iff (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 two_pos
      (SetLike.mul_mem_graded (ι_mem_homogeneousSubmodule R M (b i))
        (ι_mem_homogeneousSubmodule R M (b j))))] at e
  obtain ⟨N, hN⟩ := e
  exact sub_eq_zero.mp ((((isRegular_ι_basis b i).mul (isRegular_ι_basis b j)).pow N
    ).left.mul_left_eq_zero_iff.mp hN)

/-- **Every global section of `𝒪(n)` is a function `q / 1`.** For a coordinate `Xᵢ` there are a
`k` and an element `q` of `A` such that `Xᵢ ^ k * q` is a form of degree `k + n` and the section
takes the value `q / 1` at every point. -/
private theorem exists_forall_apply_eq (b : Module.Basis κ R M) [Nontrivial κ] {n : ℤ}
    (i : κ) (s : Γ(Proj.twistingSheaf 𝒜 n, ⊤)) :
    ∃ (k j : ℕ) (_ : (j : ℤ) = k + n) (q : _root_.SymmetricAlgebra R M),
      ι R M (b i) ^ k * q ∈ 𝒜 j ∧ ∀ y, s.1 y = Localization.mk q 1 := by
  -- on each chart `D₊(Xₗ)`, the section is a fraction `r l / Xₗ ^ k l`
  choose k j h r hr H using fun l : κ ↦ Proj.twistingSheaf.exists_eq_const_basicOpen
    (ι_mem_homogeneousSubmodule R M (b l)) one_pos
    ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s)
  have hrel (l l' : κ) : ι R M (b l') ^ k l' * r l = ι R M (b l) ^ k l * r l' :=
    mul_eq_mul_of_restrict_eq b (h l) (h l') (hr l) (hr l') _ _ _ _ s (H l) (H l')
  -- a second coordinate shows that `Xᵢ ^ k i` divides `r i`
  obtain ⟨i', hi'⟩ := exists_ne i
  obtain ⟨q, hq⟩ := (ι_basis_pow_dvd_ι_basis_pow_mul_iff b hi'.symm).mp ⟨r i', hrel i i'⟩
  -- then every numerator is `r l = Xₗ ^ k l * q`
  have hrq (l : κ) : r l = ι R M (b l) ^ k l * q :=
    ((isRegular_ι_basis b i).pow (k i)).left <| by
      beta_reduce
      rw [← hrel, hq]; ring
  refine ⟨k i, j i, by simpa using h i, q, hq ▸ hr i, fun y ↦ ?_⟩
  obtain ⟨l, hl⟩ : ∃ l, y.1 ∈ Proj.basicOpen 𝒜 (ι R M (b l)) := by
    have hy : y.1 ∈ ⨆ l, Proj.basicOpen 𝒜 (ι R M (b l)) := by
      rw [iSup_basicOpen_ι_eq_top R M b b.span_eq]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  have e := Proj.twistingSheaf.res_apply (homOfLE (le_top (a := Proj.basicOpen 𝒜 (ι R M (b l))))) s
    ⟨y.1, hl⟩
  rw [H l] at e
  refine e.symm.trans ((Proj.twistingSheaf.const_apply ..).trans
    (Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1, ?_⟩)))
  simp [hrq l, mul_comm]

/-- **Twisting sheaves of negative degree have no global sections** on projective space: for
`n < 0`, every global section of `𝒪(n)` on `Proj (Sym M)`, with `M` free of rank at least two,
vanishes. -/
theorem twistingSheaf_top_eq_zero_of_neg {n : ℤ} (hn : n < 0) (b : Module.Basis κ R M)
    [Nontrivial κ] (s : Γ(Proj.twistingSheaf 𝒜 n, ⊤)) : s = 0 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty κ)
  obtain ⟨k, j, hj, q, hq, hs⟩ := exists_forall_apply_eq b i s
  -- `Xᵢ ^ k * q` is a form of degree `j < k`, so it vanishes
  have hpow : ι R M (b i) ^ k ∈ 𝒜 k := by
    simpa using SetLike.pow_mem_graded k (ι_mem_homogeneousSubmodule R M (b i))
  have hq0 : ι R M (b i) ^ k * q = 0 := by
    rw [← DirectSum.decompose_of_mem_same 𝒜 hq,
      DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hpow (by omega)]
  ext y
  rw [hs, ((isRegular_ι_basis b i).pow k).left.mul_left_eq_zero_iff.mp hq0, Localization.mk_zero]
  exact (Proj.twistingSheaf.zero_apply y).symm

/-- **The global sections of `𝒪(j)` on projective space are the forms of degree `j`**: for
`M` free of rank at least two, the map `r ↦ r / 1` from the homogeneous elements of degree `j` of
`Sym M` to `Γ(Proj (Sym M), 𝒪(j))` is bijective. -/
theorem bijective_toTwistingSheaf_top (j : ℕ) (b : Module.Basis κ R M) [Nontrivial κ] :
    Function.Bijective (Proj.toTwistingSheaf 𝒜 (rfl : (j : ℤ) = j) ⊤) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty κ)
  have hpow (k : ℕ) : ι R M (b i) ^ k ∈ 𝒜 k := by
    simpa using SetLike.pow_mem_graded k (ι_mem_homogeneousSubmodule R M (b i))
  refine ⟨(injective_iff_map_eq_zero _).mpr fun r hr ↦ ?_, fun s ↦ ?_⟩
  · -- on `D₊(Xᵢ)`, the fraction `r / 1` vanishes only if a power of `Xᵢ` kills `r`
    have e := congrArg ((Proj.twistingSheaf 𝒜 j).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (ι R M (b i))))).op) hr
    rw [Proj.res_toTwistingSheaf, map_zero, Proj.toTwistingSheaf_eq_const,
      Proj.twistingSheaf.const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos
        (ι_mem_homogeneousSubmodule R M (b i)))] at e
    obtain ⟨N, hN⟩ := e
    exact Subtype.ext (((isRegular_ι_basis b i).pow N).left.mul_left_eq_zero_iff.mp hN)
  · obtain ⟨k, j', hj', q, hq, hs⟩ := exists_forall_apply_eq b i s
    -- comparing components of degree `k + j`, the element `q` is a form of degree `j`
    have hqj : q = DirectSum.decompose 𝒜 q j := by
      refine ((isRegular_ι_basis b i).pow k).left ?_
      beta_reduce
      rw [← DirectSum.decompose_of_mem_same 𝒜 hq,
        DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒜 (hpow k) (by omega),
        show j' - k = j by omega]
    refine ⟨⟨q, hqj ▸ (DirectSum.decompose 𝒜 q j).2⟩, Proj.twistingSheaf.ext fun y ↦ ?_⟩
    exact (Proj.toTwistingSheaf_apply_apply ..).trans (hs y).symm

/-- **The global sections of `𝒪(j)` on projective space are the forms of degree `j`**, as an
additive isomorphism `A_j ≃+ Γ(Proj A, 𝒪(j))` sending `r` to `r / 1`, for `A = Sym M` and `M` free
of rank at least two. -/
def homogeneousSubmoduleEquivTwistingSheafTop (j : ℕ) (b : Module.Basis κ R M) [Nontrivial κ] :
    𝒜 j ≃+ Γ(Proj.twistingSheaf 𝒜 j, ⊤) :=
  AddEquiv.ofBijective _ (bijective_toTwistingSheaf_top j b)

@[simp]
theorem homogeneousSubmoduleEquivTwistingSheafTop_apply (j : ℕ) (b : Module.Basis κ R M)
    [Nontrivial κ] (r : 𝒜 j) :
    homogeneousSubmoduleEquivTwistingSheafTop j b r =
      Proj.toTwistingSheaf 𝒜 (rfl : (j : ℤ) = j) ⊤ r :=
  (rfl)

end TauCeti.SymmetricAlgebra
