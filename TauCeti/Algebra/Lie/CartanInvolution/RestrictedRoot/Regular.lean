/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Decomposition
public import Mathlib.Algebra.Module.Submodule.Union

/-!
# Regular elements of a maximal abelian subspace of `𝔭`

Let `𝔞` be a submodule of a Lie algebra `𝔤₀`. An element `H ∈ 𝔞` is *regular* when no restricted
root vanishes on it: `λ(H) ≠ 0` for every `λ ∈ Σ`. There are finitely many restricted roots, so
over an infinite field a regular element exists: it avoids finitely many hyperplanes of `𝔞`.

If the restricted root spaces span `𝔤₀`, as they do for an abelian subspace of the `-1`-eigenspace
`𝔭` of a Cartan involution `θ`, then the centralizer `ker (ad H)` of a regular `H` is the
centralizer `𝔤_0` of all of `𝔞`. For `𝔞` maximal abelian in `𝔭` this gives `Z_𝔭(H) = 𝔞`: a regular
element determines `𝔞` as its centralizer in `𝔭`. Conversely, an abelian subspace of `𝔭`
containing some `H` with `Z_𝔭(H)` inside it is maximal abelian.

So a maximal abelian subspace `𝔞'` of `𝔭` with `Z_𝔭(H') ⊆ 𝔞'` is the only maximal abelian subspace
of `𝔭` containing `H'`. This is the Lie algebra step of the conjugacy of maximal abelian
subspaces: if an isomorphism `e` carries `H'` into a maximal abelian subspace `𝔞` of the `𝔭` of
`e ∘ θ ∘ e⁻¹`, then `e` carries `𝔞'` onto `𝔞`. Applied to an automorphism commuting with `θ`
(an element of `K_θ`) that moves `H'` into `𝔞`, it reduces the conjugacy of any two maximal
abelian subspaces of `𝔭` to the statement that every element of `𝔭` is `K_θ`-conjugate into `𝔞`.

## Main results

* `Submodule.exists_forall_restrictedRoots_apply_ne_zero`: a finite-dimensional Lie algebra over an
  infinite field has a regular element in each submodule `𝔞`.
* `Submodule.ker_ad_eq_restrictedRootSpace_zero`: if the restricted root spaces span `𝔤₀`, the
  centralizer of a regular `H` is `𝔤_0`.
* `LieEquiv.IsCartanInvolution.ker_ad_eq_restrictedRootSpace_zero`: the same for an abelian
  subspace of `𝔭` of a Cartan involution.
* `LieEquiv.IsMaximalAbelianInP.ker_ad_inf_cartanP_eq`: for `𝔞` maximal abelian in `𝔭` and `H`
  regular, `Z_𝔭(H) = 𝔞`; `LieEquiv.IsMaximalAbelianInP.exists_ker_ad_inf_cartanP_eq` gives such an
  `H`.
* `LieEquiv.isMaximalAbelianInP_of_ker_ad_inf_cartanP_le` and
  `LieEquiv.IsCartanInvolution.isMaximalAbelianInP_iff_exists_ker_ad_inf_cartanP_eq`: an abelian
  subspace of `𝔭` is maximal exactly when it is the centralizer in `𝔭` of one of its elements.
* `LieEquiv.IsMaximalAbelianInP.eq_of_ker_ad_inf_cartanP_le`: a maximal abelian subspace `𝔟` of
  `𝔭` containing `H` lies in, hence equals, any maximal abelian `𝔞 ⊇ Z_𝔭(H)`.
* `LieEquiv.IsMaximalAbelianInP.map_eq_of_apply_mem`: an isomorphism carrying `H'` with
  `Z_𝔭(H') ⊆ 𝔞'` into a maximal abelian subspace `𝔞` carries `𝔞'` onto `𝔞`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4 and Theorem 6.51.
* J.-H. Eschenburg, *Lecture Notes on Symmetric Spaces*, §9, Theorem 9 and the Lemma after it.
-/

public section

open LieAlgebra Module

namespace Submodule

/-- **Regular elements exist.** For a submodule `𝔞` of a finite-dimensional Lie algebra over an
infinite field, some `H ∈ 𝔞` lies on none of the root hyperplanes `ker λ`, `λ ∈ Σ`. -/
theorem exists_forall_restrictedRoots_apply_ne_zero {K L : Type*} [Field K] [Infinite K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] (𝔞 : Submodule K L) :
    ∃ H : 𝔞, ∀ μ ∈ 𝔞.restrictedRoots, μ H ≠ 0 := by
  have : Finite 𝔞.restrictedRoots := finite_restrictedRoots.to_subtype
  obtain ⟨H, hH⟩ := Dual.exists_forall_ne_zero_of_forall_exists
    (fun μ : 𝔞.restrictedRoots ↦ (μ : Dual K 𝔞)) fun μ ↦ by
      by_contra! h
      exact (mem_restrictedRoots.mp μ.property).1 (LinearMap.ext h)
  exact ⟨H, fun μ hμ ↦ hH ⟨μ, hμ⟩⟩

variable {R L : Type*} [CommRing R] [IsDomain R] [LieRing L] [LieAlgebra R L] [IsTorsionFree R L]
  {𝔞 : Submodule R L}

/-- **The centralizer of a regular element.** If the restricted root spaces of `𝔞` span `𝔤₀` and
no restricted root vanishes on `H ∈ 𝔞`, then the centralizer `ker (ad H)` of `H` is the
centralizer `𝔤_0` of `𝔞`. -/
theorem ker_ad_eq_restrictedRootSpace_zero
    (hspan : ⨆ μ : Dual R 𝔞, 𝔞.restrictedRootSpace μ = ⊤) {H : 𝔞}
    (hH : ∀ μ ∈ 𝔞.restrictedRoots, μ H ≠ 0) :
    LinearMap.ker (ad R L (H : L)) = 𝔞.restrictedRootSpace 0 := by
  set f : End R L := ad R L H
  set E := ⨆ c ∈ ({0}ᶜ : Set R), f.eigenspace c
  have h0 : 𝔞.restrictedRootSpace 0 ≤ LinearMap.ker f :=
    fun x hx ↦ LinearMap.mem_ker.mpr (mem_restrictedRootSpace_zero.mp hx H)
  -- Every restricted root space other than `𝔤_0` lies in an eigenspace of `ad H` with nonzero
  -- eigenvalue, so `𝔤₀ = 𝔤_0 ⊔ E`, and `E` meets the kernel of `ad H` trivially.
  have htop : 𝔞.restrictedRootSpace 0 ⊔ E = ⊤ := by
    refine eq_top_iff.mpr (hspan.symm.le.trans (iSup_le fun μ ↦ ?_))
    by_cases hμ0 : μ = 0
    · exact hμ0 ▸ le_sup_left
    by_cases hbot : 𝔞.restrictedRootSpace μ = ⊥
    · exact hbot.le.trans bot_le
    refine le_sup_of_le_right
      (le_iSup₂_of_le (μ H) (hH μ (mem_restrictedRoots.mpr ⟨hμ0, hbot⟩)) ?_)
    rw [restrictedRootSpace_eq_iInf]
    exact iInf_le _ H
  have hdisj : Disjoint (LinearMap.ker f) E := by
    have := (End.eigenspaces_iSupIndep f).disjoint_biSup (y := {0}ᶜ) (x := 0) (by simp)
    rwa [End.eigenspace_zero] at this
  refine le_antisymm ?_ h0
  rw [← inf_top_eq (LinearMap.ker f), ← htop, inf_comm, sup_inf_assoc_of_le _ h0,
    hdisj.symm.eq_bot, sup_bot_eq]

end Submodule

namespace LieEquiv

open Submodule

section Generic

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {θ : L ≃ₗ⁅R⁆ L}
  {𝔞 𝔟 : Submodule R L} {H : L}

/-- An abelian subspace of `𝔭` lies in the centralizer in `𝔭` of each of its elements. -/
private theorem le_ker_ad_inf_cartanP (h𝔟 : 𝔟 ≤ θ.cartanP) (hab : ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0)
    (hH : H ∈ 𝔟) : 𝔟 ≤ LinearMap.ker (ad R L H) ⊓ θ.cartanP :=
  fun _ hx ↦ ⟨LinearMap.mem_ker.mpr (hab H hH _ hx), h𝔟 hx⟩

/-- An abelian subspace `𝔞` of `𝔭` that contains the centralizer `Z_𝔭(H)` of one of its elements
`H` is maximal abelian in `𝔭`. -/
theorem isMaximalAbelianInP_of_ker_ad_inf_cartanP_le (h𝔞 : 𝔞 ≤ θ.cartanP)
    (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) (hH𝔞 : H ∈ 𝔞)
    (hH : LinearMap.ker (ad R L H) ⊓ θ.cartanP ≤ 𝔞) : θ.IsMaximalAbelianInP 𝔞 :=
  isMaximalAbelianInP_iff.mpr ⟨⟨h𝔞, hab⟩, fun _ h𝔟 h𝔞𝔟 ↦
    (le_ker_ad_inf_cartanP h𝔟.1 h𝔟.2 (h𝔞𝔟 hH𝔞)).trans hH⟩

/-- **Uniqueness of the maximal abelian subspace through `H`.** If a maximal abelian subspace `𝔞`
of `𝔭` contains the centralizer `Z_𝔭(H)`, then every maximal abelian subspace of `𝔭` containing
`H` equals `𝔞`. -/
theorem IsMaximalAbelianInP.eq_of_ker_ad_inf_cartanP_le (h𝔞 : θ.IsMaximalAbelianInP 𝔞)
    (h𝔟 : θ.IsMaximalAbelianInP 𝔟) (hH𝔟 : H ∈ 𝔟)
    (hH : LinearMap.ker (ad R L H) ⊓ θ.cartanP ≤ 𝔞) : 𝔟 = 𝔞 := by
  have h𝔟𝔞 : 𝔟 ≤ 𝔞 :=
    (le_ker_ad_inf_cartanP h𝔟.le_cartanP (fun _ hx _ hy ↦ h𝔟.lie_eq_zero hx hy) hH𝔟).trans hH
  exact le_antisymm h𝔟𝔞 ((isMaximalAbelianInP_iff.mp h𝔟).2
    ⟨h𝔞.le_cartanP, fun _ hx _ hy ↦ h𝔞.lie_eq_zero hx hy⟩ h𝔟𝔞)

variable {L' : Type*} [LieRing L'] [LieAlgebra R L'] in
/-- **Conjugating maximal abelian subspaces through a regular element.** Let `𝔞` be a maximal
abelian subspace of `𝔭` and `H` an element whose centralizer `Z_𝔭(H)` lies in `𝔞`. If an
isomorphism `e` carries `H` into a maximal abelian subspace `𝔟` of the `-1`-eigenspace of
`e ∘ θ ∘ e⁻¹`, then `e` carries `𝔞` onto `𝔟`. For an automorphism `e` commuting with `θ` this
says that `e 𝔞 = 𝔟` as soon as `e H ∈ 𝔟`. -/
theorem IsMaximalAbelianInP.map_eq_of_apply_mem (h𝔞 : θ.IsMaximalAbelianInP 𝔞)
    (hH : LinearMap.ker (ad R L H) ⊓ θ.cartanP ≤ 𝔞) (e : L ≃ₗ⁅R⁆ L') {𝔟 : Submodule R L'}
    (h𝔟 : (e.conj θ).IsMaximalAbelianInP 𝔟) (he : e H ∈ 𝔟) :
    𝔞.map (e.toLinearEquiv : L →ₗ[R] L') = 𝔟 := by
  set f := e.toLinearEquiv
  -- The centralizer in `𝔭` of `e H` is the image of that of `H`.
  have hker :
      LinearMap.ker (ad R L' (e H)) = (LinearMap.ker (ad R L H)).map (f : L →ₗ[R] L') := by
    ext y
    refine ⟨fun hy ↦ ⟨e.symm y, ?_, by simp [f]⟩, ?_⟩
    · rw [LinearMap.mem_ker, ad_apply] at hy
      rw [SetLike.mem_coe, LinearMap.mem_ker, ad_apply, ← e.symm_apply_apply H, ← e.symm.map_lie,
        hy, map_zero]
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ad_apply] at hx
      simp [f, ← LieEquiv.map_lie, hx]
  refine ((h𝔞.map e).eq_of_ker_ad_inf_cartanP_le h𝔟 he ?_).symm
  rw [hker, cartanP_conj, ← map_inf _ f.injective]
  exact map_mono hH

end Generic

namespace IsCartanInvolution

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}

/-- **The centralizer of a regular element.** For a Cartan involution `θ`, an abelian subspace `𝔞`
of `𝔭` and `H ∈ 𝔞` on which no restricted root vanishes, the centralizer `ker (ad H)` of `H` is the
centralizer `𝔤_0` of `𝔞`. -/
theorem ker_ad_eq_restrictedRootSpace_zero (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)
    (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) {H : 𝔞} (hH : ∀ μ ∈ 𝔞.restrictedRoots, μ H ≠ 0) :
    LinearMap.ker (ad ℝ L (H : L)) = 𝔞.restrictedRootSpace 0 :=
  Submodule.ker_ad_eq_restrictedRootSpace_zero (hθ.iSup_restrictedRootSpace_eq_top h𝔞 hab) hH

end IsCartanInvolution

namespace IsMaximalAbelianInP

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}

/-- **A regular element determines `𝔞`.** For a Cartan involution `θ`, a maximal abelian
subspace `𝔞` of `𝔭` and `H ∈ 𝔞` on which no restricted root vanishes, the centralizer of `H` in
`𝔭` is `𝔞`. -/
theorem ker_ad_inf_cartanP_eq (h𝔞 : θ.IsMaximalAbelianInP 𝔞) (hθ : θ.IsCartanInvolution) {H : 𝔞}
    (hH : ∀ μ ∈ 𝔞.restrictedRoots, μ H ≠ 0) :
    LinearMap.ker (ad ℝ L (H : L)) ⊓ θ.cartanP = 𝔞 := by
  rw [hθ.ker_ad_eq_restrictedRootSpace_zero h𝔞.le_cartanP
    (fun _ hx _ hy ↦ h𝔞.lie_eq_zero hx hy) hH, h𝔞.restrictedRootSpace_zero_inf_cartanP]

/-- For a Cartan involution `θ`, a maximal abelian subspace `𝔞` of `𝔭` is the centralizer in `𝔭`
of one of its elements, any element on which no restricted root vanishes. -/
theorem exists_ker_ad_inf_cartanP_eq (h𝔞 : θ.IsMaximalAbelianInP 𝔞) (hθ : θ.IsCartanInvolution) :
    ∃ H ∈ 𝔞, LinearMap.ker (ad ℝ L H) ⊓ θ.cartanP = 𝔞 := by
  have := hθ.finiteDimensional
  obtain ⟨H, hH⟩ := 𝔞.exists_forall_restrictedRoots_apply_ne_zero
  exact ⟨H, H.property, h𝔞.ker_ad_inf_cartanP_eq hθ hH⟩

end IsMaximalAbelianInP

/-- **Maximal abelian subspaces of `𝔭` are centralizers.** For a Cartan involution `θ`, a
submodule `𝔞` is maximal abelian in `𝔭` exactly when it is an abelian subspace of `𝔭` equal to
the centralizer in `𝔭` of one of its elements. -/
theorem IsCartanInvolution.isMaximalAbelianInP_iff_exists_ker_ad_inf_cartanP_eq {L : Type*}
    [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {𝔞 : Submodule ℝ L} :
    θ.IsMaximalAbelianInP 𝔞 ↔ (𝔞 ≤ θ.cartanP ∧ ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) ∧
      ∃ H ∈ 𝔞, LinearMap.ker (ad ℝ L H) ⊓ θ.cartanP = 𝔞 :=
  ⟨fun h𝔞 ↦ ⟨⟨h𝔞.le_cartanP, fun _ hx _ hy ↦ h𝔞.lie_eq_zero hx hy⟩,
    h𝔞.exists_ker_ad_inf_cartanP_eq hθ⟩,
    fun ⟨⟨h𝔞, hab⟩, _, hH𝔞, hH⟩ ↦ isMaximalAbelianInP_of_ker_ad_inf_cartanP_le h𝔞 hab hH𝔞 hH.le⟩

end LieEquiv
