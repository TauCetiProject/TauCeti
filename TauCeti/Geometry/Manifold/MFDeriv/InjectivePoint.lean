/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Immersion.Family
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity

/-!
# Injective points and somewhere injective maps

A point `x` is an **injective point** of a map `f : M → N` between manifolds when the manifold
derivative `mfderiv I I' f x` is injective and no other point of `M` has the image `f x`
(`TauCeti.IsInjectivePoint`). A map is **somewhere injective** when it has an injective point
(`TauCeti.IsSomewhereInjective`). This is the notion of Wendl's *Lectures on holomorphic curves*,
Definition 4.5, for maps from Riemann surfaces into almost complex manifolds, where it
characterizes the simple curves among the nonconstant closed pseudoholomorphic curves and is the
condition under which the transversality theory of moduli spaces of curves applies.

At a point where `f` is not differentiable, Mathlib's `mfderiv` is `0`, which is not injective
unless the model space of `M` is trivial; so an injective point is a point of differentiability
(`TauCeti.IsInjectivePoint.mdifferentiableAt`), as the definition intends.

Injective points compose: if `x` is an injective point of `f` and `f x` one of `g`, then `x` is
an injective point of `g ∘ f` (`TauCeti.IsInjectivePoint.comp`). Every point is an injective point
of a `C^n` diffeomorphism, `n ≠ 0` (`Diffeomorph.isInjectivePoint`), so composing with a
diffeomorphism on either side preserves injective points and somewhere injectivity
(`Diffeomorph.isInjectivePoint_comp_diffeomorph_iff`,
`Diffeomorph.isInjectivePoint_diffeomorph_comp_iff`,
`Diffeomorph.isSomewhereInjective_comp_diffeomorph_iff`,
`Diffeomorph.isSomewhereInjective_diffeomorph_comp_iff`). For curves these are the
reparametrization by a biholomorphism of the source and the transport by a diffeomorphism of the
target intertwining the almost complex structures.

## Main definitions

* `TauCeti.IsInjectivePoint I I' f x`: `x` is an injective point of `f`.
* `TauCeti.IsSomewhereInjective I I' f`: `f` has an injective point.

## References

* C. Wendl, *Lectures on holomorphic curves in symplectic and contact geometry*,
  arXiv:1011.1690, Definition 4.5.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012, §2.5.
-/

public section

open Filter Function Set
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {I'' : ModelWithCorners 𝕜 E'' H''}
  {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
  [ChartedSpace H' N] [TopologicalSpace N'] [ChartedSpace H'' N']

namespace TauCeti

variable (I I') in
/-- A point `x` is an **injective point** of `f : M → N` when the manifold derivative of `f` at `x`
is injective and `x` is the only point of `M` with image `f x`. Since `mfderiv` is `0` where `f` is
not differentiable, an injective point is a point of differentiability whenever the model space of
`M` is nontrivial. -/
structure IsInjectivePoint (f : M → N) (x : M) : Prop where
  /-- The manifold derivative at an injective point is injective. -/
  injective_mfderiv : Injective (mfderiv I I' f x)
  /-- An injective point is the only point with its image. -/
  eq_of_apply_eq ⦃y : M⦄ : f y = f x → y = x

variable (I I') in
/-- A map `f : M → N` is **somewhere injective** when it has an injective point: a point `x` at
which the manifold derivative is injective and which is the only point with image `f x`. -/
def IsSomewhereInjective (f : M → N) : Prop :=
  ∃ x, IsInjectivePoint I I' f x

variable {f : M → N} {x : M}

theorem isInjectivePoint_iff :
    IsInjectivePoint I I' f x ↔ Injective (mfderiv I I' f x) ∧ f ⁻¹' {f x} = {x} := by
  refine ⟨fun h ↦ ⟨h.injective_mfderiv, ?_⟩, fun h ↦ ⟨h.1, fun y hy ↦ ?_⟩⟩
  · ext y
    exact ⟨fun hy ↦ h.eq_of_apply_eq hy, fun hy ↦ hy ▸ rfl⟩
  · have hy' : y ∈ f ⁻¹' {f x} := hy
    rwa [h.2] at hy'

theorem isSomewhereInjective_iff :
    IsSomewhereInjective I I' f ↔ ∃ x, IsInjectivePoint I I' f x :=
  Iff.rfl

namespace IsInjectivePoint

/-- The fibre of `f` through an injective point `x` is `{x}`. -/
theorem preimage_singleton (h : IsInjectivePoint I I' f x) : f ⁻¹' {f x} = {x} :=
  (isInjectivePoint_iff.1 h).2

/-- A point other than an injective point `x` has an image different from `f x`. -/
theorem apply_ne (h : IsInjectivePoint I I' f x) {y : M} (hy : y ≠ x) : f y ≠ f x :=
  fun hxy ↦ hy (h.eq_of_apply_eq hxy)

/-- A map is differentiable at each of its injective points. -/
theorem mdifferentiableAt (h : IsInjectivePoint I I' f x) : MDifferentiableAt I I' f x :=
  mdifferentiableAt_of_mfderiv_injective h.injective_mfderiv

/-- A map with an injective point is somewhere injective. -/
theorem isSomewhereInjective (h : IsInjectivePoint I I' f x) : IsSomewhereInjective I I' f :=
  ⟨x, h⟩

/-- **Injective points compose.** If `x` is an injective point of `f` and `f x` is an injective
point of `g`, then `x` is an injective point of `g ∘ f`. -/
theorem comp {g : N → N'} (hg : IsInjectivePoint I' I'' g (f x)) (hf : IsInjectivePoint I I' f x) :
    IsInjectivePoint I I'' (g ∘ f) x where
  injective_mfderiv := by
    rw [mfderiv_comp x hg.mdifferentiableAt hf.mdifferentiableAt, ContinuousLinearMap.coe_comp]
    exact hg.injective_mfderiv.comp hf.injective_mfderiv
  eq_of_apply_eq _ hy := hf.eq_of_apply_eq (hg.eq_of_apply_eq hy)

end IsInjectivePoint

/-- **The injective points of a map from a compact manifold form an open set.** For a `C^n` map,
`1 ≤ n`, from a compact manifold modelled on a finite-dimensional space over `ℝ` or `ℂ` to a
Hausdorff manifold, the set of injective points is open. -/
theorem isOpen_setOf_isInjectivePoint [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E]
    [IsManifold I 1 M] [IsManifold I' 1 N] [CompactSpace M] [T2Space N] {n : WithTop ℕ∞}
    (hf : ContMDiff I I' n f) (hn : 1 ≤ n) : IsOpen {x | IsInjectivePoint I I' f x} := by
  let := IsRCLikeNormedField.rclike 𝕜
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  -- `f` is injective on a neighbourhood `t` of `x`, and its derivative stays injective near `x`.
  obtain ⟨t, ht, hinj⟩ :=
    (hf x).exists_mem_nhds_injOn (zero_lt_one.trans_le hn).ne' hx.injective_mfderiv
  have hF : ContMDiffAt (I.prod I) I' n (uncurry fun (_ : M) ↦ f) (x, x) :=
    (hf x).comp (x, x) contMDiffAt_snd
  have hD : ∀ᶠ y in 𝓝 x, Injective (mfderiv I I' f y) :=
    ((continuous_id.prodMk continuous_id).tendsto x).eventually
      (hF.eventually_injective_mfderiv hn hx.injective_mfderiv)
  -- The image of the compact complement of the interior of `t` avoids `f x`, so the fibres
  -- through the points near `x` lie in `t`.
  have hK : IsCompact (interior t)ᶜ := isOpen_interior.isClosed_compl.isCompact
  have hfK : f x ∉ f '' (interior t)ᶜ := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hx.eq_of_apply_eq hyx ▸ mem_interior_iff_mem_nhds.2 ht)
  have hU : f ⁻¹' (f '' (interior t)ᶜ)ᶜ ∈ 𝓝 x := (hf x).continuousAt.preimage_mem_nhds
    ((hK.image hf.continuous).isClosed.isOpen_compl.mem_nhds hfK)
  filter_upwards [ht, hU, hD] with y hyt hyU hyD
  refine ⟨hyD, fun w hw ↦ hinj ?_ hyt hw⟩
  by_contra hwt
  exact hyU ⟨w, fun hw' ↦ hwt (interior_subset hw'), hw⟩

end TauCeti

namespace Diffeomorph

open TauCeti

variable {n : WithTop ℕ∞}

/-- Every point is an injective point of a `C^n` diffeomorphism, `n ≠ 0`. -/
theorem isInjectivePoint (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) (x : M) :
    IsInjectivePoint I I' Φ x where
  injective_mfderiv := (Φ.isInvertible_mfderiv hn).injective
  eq_of_apply_eq _ hy := Φ.injective hy

/-- Precomposing with a `C^n` diffeomorphism `Φ`, `n ≠ 0`, carries the injective points of `f`
at `Φ x` to injective points of `f ∘ Φ` at `x`, and conversely. -/
theorem isInjectivePoint_comp_diffeomorph_iff (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) {f : N → N'}
    {x : M} : IsInjectivePoint I I'' (f ∘ Φ) x ↔ IsInjectivePoint I' I'' f (Φ x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp (Φ.isInjectivePoint hn x)⟩
  have h₀ : IsInjectivePoint I I'' (f ∘ Φ) (Φ.symm (Φ x)) := by rwa [Φ.symm_apply_apply]
  have h' := h₀.comp (Φ.symm.isInjectivePoint hn (Φ x))
  rwa [comp_assoc, show ⇑Φ ∘ Φ.symm = id from funext Φ.apply_symm_apply, comp_id] at h'

/-- Postcomposing with a `C^n` diffeomorphism `Ψ`, `n ≠ 0`, does not change the injective points
of a map. -/
theorem isInjectivePoint_diffeomorph_comp_iff (Ψ : N ≃ₘ^n⟮I', I''⟯ N') (hn : n ≠ 0) {f : M → N}
    {x : M} : IsInjectivePoint I I'' (Ψ ∘ f) x ↔ IsInjectivePoint I I' f x := by
  refine ⟨fun h ↦ ?_, fun h ↦ (Ψ.isInjectivePoint hn (f x)).comp h⟩
  have h' := (Ψ.symm.isInjectivePoint hn ((Ψ ∘ f) x)).comp h
  rwa [← comp_assoc, show Ψ.symm ∘ ⇑Ψ = id from funext Ψ.symm_apply_apply, id_comp] at h'

/-- Precomposing with a `C^n` diffeomorphism, `n ≠ 0`, preserves somewhere injectivity. -/
theorem isSomewhereInjective_comp_diffeomorph_iff (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0)
    {f : N → N'} : IsSomewhereInjective I I'' (f ∘ Φ) ↔ IsSomewhereInjective I' I'' f := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨Φ x, (Φ.isInjectivePoint_comp_diffeomorph_iff hn).1 hx⟩,
    fun ⟨y, hy⟩ ↦ ⟨Φ.symm y, (Φ.isInjectivePoint_comp_diffeomorph_iff hn).2 ?_⟩⟩
  rwa [Φ.apply_symm_apply]

/-- Postcomposing with a `C^n` diffeomorphism, `n ≠ 0`, preserves somewhere injectivity. -/
theorem isSomewhereInjective_diffeomorph_comp_iff (Ψ : N ≃ₘ^n⟮I', I''⟯ N') (hn : n ≠ 0)
    {f : M → N} : IsSomewhereInjective I I'' (Ψ ∘ f) ↔ IsSomewhereInjective I I' f :=
  exists_congr fun _ ↦ Ψ.isInjectivePoint_diffeomorph_comp_iff hn

end Diffeomorph
