/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.AlmostComplex
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Seam-compatible vertical families and compatible structures on a symplectic suspension

Let `φ` be a symplectomorphism of a finite-dimensional manifold `M` with symplectic form `σ`,
let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its mapping torus and let
`X_φ = (ℝ / ℤ)_s × Y_φ` carry the form `Ω = ds ∧ dt + σ_v`. A block almost complex structure on
`X_φ` descends from a vertical family `K_((s,t),x)` of almost complex structures on `T_x M` which
is periodic in `s` and satisfies the seam identity `K_(t + 1) = φ^* K_t`
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`). This file constructs such a
family from a single `σ`-compatible almost complex structure `J₀` on `M`; no `φ`-invariant
structure is needed.

Write `J_k = (φ ^ k)^* J₀` for `k ∈ ℤ` (`TauCeti.SmoothMappingTorus.seamStructure`), which are
all `σ`-compatible, and `J_(k + 1) = φ^* J_k`. On the time interval `[k, k + 1]` the family is the
smooth Cayley path from `J_k` to `J_(k + 1)`, reparametrized to be constant on the collars
`[k, k + 1/3]` and `[k + 2/3, k + 1]`:

`K_((s,t),x) = cayleyPath J_⌊t⌋ J_(⌊t⌋ + 1) (3 (t - ⌊t⌋) - 1)` at `x`

(`TauCeti.SmoothMappingTorus.seamFamily`). Because each path is constant near the ends of its
interval, consecutive pieces agree on a neighbourhood of every integer time, so the family is
jointly smooth. By naturality of the Cayley path under pullback, the piece on `[k + 1, k + 2]` is
the pullback by `φ` of the piece on `[k, k + 1]`, which is the seam identity. The family is
`σ`-compatible everywhere and equals `J₀` for `|t| ≤ 1/3`.

The descended structure `TauCeti.SmoothMappingTorus.seamAlmostComplexStructure` on `X_φ` is
therefore smooth and compatible with `Ω`, sends `∂_s` to the suspension vector field `T = ∂_t`,
and restricts to `J₀` on the vertical tangent spaces of the fibres over times `t` with
`|t| ≤ 1/3`.

The construction depends smoothly on `J₀`. Let `K₀ p` be a family of `σ`-compatible structures
on `M` depending smoothly on a parameter `p` in a manifold `P`, in the sense that `(p, x) ↦ K₀ p x`
is a smooth section of the tangent endomorphism bundle along `P × M → M`. Then the vertical
families built from the `K₀ p` are jointly smooth in `(p, ((s, t), x))`
(`TauCeti.SmoothMappingTorus.contMDiff_seamFamily_family`), and the descended structures on
`X_φ` are jointly smooth in `(p, y)`
(`TauCeti.SmoothMappingTorus.contMDiff_seamAlmostComplexStructure_family`). For each `p` the
descended structure is the structure built from `K₀ p` alone, so it is compatible with `Ω`, has
block form and restricts to `K₀ p` near time zero. Neither compactness nor finite dimension of
`P` is needed. The endpoint `φ^* K₀ p` of each path is the pullback of the given family; no
separate endpoint family is chosen.

## Main definitions

* `TauCeti.SmoothMappingTorus.seamStructure hσ hJ₀ k`: the structure `(φ ^ k)^* J₀`.
* `TauCeti.SmoothMappingTorus.seamFamily hσ hJ₀`: the vertical family `K`.
* `TauCeti.SmoothMappingTorus.seamAlmostComplexStructure hσ hJ₀`: the descended block structure
  on `(ℝ / ℤ) × Y_φ`.

## Main results

* `TauCeti.SmoothMappingTorus.contMDiff_seamFamily`: the vertical family is jointly smooth.
* `TauCeti.SmoothMappingTorus.mfderiv_symm_seamFamily`: the seam identity.
* `TauCeti.SmoothMappingTorus.compatible_seamFamily`: the family is `σ`-compatible.
* `TauCeti.SmoothMappingTorus.seamFamily_of_mem_Icc`,
  `TauCeti.SmoothMappingTorus.seamFamily_eq_of_mem_Icc`: the family is `J_k` on the collar of
  width `1/3` around the integer time `k`, and `J₀` around time `0`.
* `TauCeti.SmoothMappingTorus.compatible_seamAlmostComplexStructure`: the descended structure is
  compatible with `Ω`.
* `TauCeti.SmoothMappingTorus.seamAlmostComplexStructure_mk`: in the coordinates `(s, t, x)` with
  `|t| ≤ 1/3`, it sends `a ∂_s + b ∂_t + v` to `-b ∂_s + a ∂_t + J₀ v`.
* `TauCeti.SmoothMappingTorus.contMDiff_seamFamily_family`,
  `TauCeti.SmoothMappingTorus.contMDiff_seamAlmostComplexStructure_family`: for a smooth family
  of compatible structures `K₀ p`, the vertical families and the descended structures depend
  smoothly on the parameter `p`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures on
  `ℝ × Y_φ`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (the action `J ↦ φ^* J` of symplectomorphisms on compatible almost complex
  structures).
-/

public noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M} (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
  {J₀ : SmoothAlmostComplexStructure I M} (hJ₀ : σ.Compatible J₀)

/-! ### The structures `(φ ^ k)^* J₀` -/

variable (φ J₀) in
/-- The pullback `(φ ^ k)^* J₀` of `J₀` by the `k`-th power of the symplectomorphism `φ`. -/
def seamStructure (k : ℤ) : SmoothAlmostComplexStructure I M :=
  J₀.pullback (φ ^ k)

include hσ hJ₀ in
/-- Every structure `(φ ^ k)^* J₀` is compatible with `σ`. -/
theorem compatible_seamStructure (k : ℤ) :
    σ.Compatible (seamStructure φ J₀ k) := by
  have h := hJ₀.pullback (φ ^ k)
  rwa [SmoothForm.mpullback_zpow_eq_self hσ k] at h

/-- The structure `(φ ^ 0)^* J₀` is `J₀`. -/
@[simp]
theorem seamStructure_zero : seamStructure φ J₀ 0 = J₀ := by
  rw [seamStructure, zpow_zero, Diffeomorph.one_def,
    SmoothAlmostComplexStructure.pullback_refl]

/-- Consecutive structures differ by a pullback along `φ`: `J_(k + 1) = φ^* J_k`. -/
theorem seamStructure_add_one (k : ℤ) :
    seamStructure φ J₀ (k + 1) =
      (seamStructure φ J₀ k).pullback φ := by
  rw [seamStructure, seamStructure, zpow_add_one, Diffeomorph.mul_def,
    SmoothAlmostComplexStructure.pullback_trans]

/-! ### The pieces of the vertical family -/

/-- The piece of the vertical family on the time interval `[k, k + 1]`: the smooth Cayley path
from `J_k` to `J_(k + 1)`, constant for `t ≤ k + 1/3` and for `t ≥ k + 2/3`. -/
def seamPath (k : ℤ) (t : ℝ) : SmoothAlmostComplexStructure I M :=
  (compatible_seamStructure hσ hJ₀ k).cayleyPath (compatible_seamStructure hσ hJ₀ (k + 1))
    (3 * (t - k) - 1)

/-- On the collar `t ≤ k + 1/3` the piece on `[k, k + 1]` is `J_k`. -/
theorem seamPath_of_le {k : ℤ} {t : ℝ} (ht : t ≤ k + 1 / 3) :
    seamPath hσ hJ₀ k t = seamStructure φ J₀ k :=
  SmoothTwoForm.Compatible.cayleyPath_of_nonpos _ _ (by linarith)

/-- On the collar `t ≥ k + 2/3` the piece on `[k, k + 1]` is `J_(k + 1)`. -/
theorem seamPath_of_ge {k : ℤ} {t : ℝ} (ht : k + 2 / 3 ≤ t) :
    seamPath hσ hJ₀ k t = seamStructure φ J₀ (k + 1) :=
  SmoothTwoForm.Compatible.cayleyPath_of_one_le _ _ (by linarith)

/-- Consecutive pieces agree, with value `J_k`, on the collar of width `1/3` around `k`. -/
theorem seamPath_sub_one {k : ℤ} {t : ℝ} (ht : t ∈ Icc ((k : ℝ) - 1 / 3) (k + 1 / 3)) :
    seamPath hσ hJ₀ (k - 1) t = seamPath hσ hJ₀ k t := by
  rw [seamPath_of_le hσ hJ₀ ht.2, seamPath_of_ge hσ hJ₀ (by push_cast; linarith [ht.1]),
    sub_add_cancel]

/-- The piece on `[k + 1, k + 2]` is the pullback by `φ` of the piece on `[k, k + 1]`. -/
theorem seamPath_add_one (k : ℤ) (t : ℝ) :
    seamPath hσ hJ₀ (k + 1) (t + 1) = (seamPath hσ hJ₀ k t).pullback φ := by
  rw [seamPath, seamPath, SmoothTwoForm.Compatible.pullback_cayleyPath]
  refine (SmoothTwoForm.Compatible.cayleyPath_congr (compatible_seamStructure hσ hJ₀ (k + 1))
    (compatible_seamStructure hσ hJ₀ (k + 1 + 1)) ((compatible_seamStructure hσ hJ₀ k).pullback φ)
    ((compatible_seamStructure hσ hJ₀ (k + 1)).pullback φ) (seamStructure_add_one k)
    (seamStructure_add_one (k + 1)) _).trans ?_
  congr 1
  push_cast
  ring

/-- Near every time `t₀`, the vertical family is given by the single piece on
`[⌊t₀⌋, ⌊t₀⌋ + 1]`, on a neighbourhood of `t₀` that does not depend on `J₀`. -/
theorem eventually_seamPath_floor_eq (t₀ : ℝ) :
    ∀ᶠ t in 𝓝 t₀, ∀ {J₀ : SmoothAlmostComplexStructure I M} (hJ₀ : σ.Compatible J₀),
      seamPath hσ hJ₀ ⌊t⌋ t = seamPath hσ hJ₀ ⌊t₀⌋ t := by
  have h₀ := Int.floor_le t₀
  have h₁ := Int.lt_floor_add_one t₀
  have hlo : (⌊t₀⌋ : ℝ) - 1 / 3 < t₀ := by linarith
  filter_upwards [Ioo_mem_nhds hlo h₁] with t ht J₀ hJ₀
  rcases le_or_gt (⌊t₀⌋ : ℝ) t with hk | hk
  · rw [Int.floor_eq_iff.2 ⟨hk, ht.2⟩]
  · have hfl : ⌊t⌋ = ⌊t₀⌋ - 1 :=
      Int.floor_eq_iff.2 ⟨by push_cast; linarith [ht.1], by push_cast; linarith⟩
    rw [hfl]
    exact seamPath_sub_one hσ hJ₀ ⟨ht.1.le, by linarith⟩

/-! ### The vertical family -/

/-- The seam-compatible vertical family on `(ℝ × ℝ) × M`: at `((s, t), x)` it is the piece
`seamPath ⌊t⌋ t` of the vertical family at `x`, independent of `s`. -/
def seamFamily (p : (ℝ × ℝ) × M) : AlmostComplexStructure (TangentSpace I p.2) :=
  (seamPath hσ hJ₀ ⌊p.1.2⌋ p.1.2).almostComplexStructureAt p.2

/-- The vertical family applied to a tangent vector. -/
theorem seamFamily_apply (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    seamFamily hσ hJ₀ p v = seamPath hσ hJ₀ ⌊p.1.2⌋ p.1.2 p.2 v :=
  SmoothAlmostComplexStructure.almostComplexStructureAt_apply _ _ _

section Family

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {K₀ : P → SmoothAlmostComplexStructure I M} (hK₀ : ∀ p, σ.Compatible (K₀ p))
  (hs : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
      ((K₀ q.1).toEndomorphism q.2)))

include hs in
/-- The structures `(φ ^ k)^* K₀ p` depend smoothly on `p` when `K₀ p` does. -/
private theorem contMDiff_seamStructure_family (k : ℤ) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((seamStructure φ (K₀ q.1) k).toEndomorphism q.2)) :=
  SmoothAlmostComplexStructure.contMDiff_pullback_family (φ ^ k) hs

include hs in
/-- For a family `K₀ p` of `σ`-compatible structures depending smoothly on a parameter `p` in a
manifold `P`, the seam-compatible vertical families built from the `K₀ p` depend smoothly on
`(p, ((s, t), x))`. -/
theorem contMDiff_seamFamily_family :
    ContMDiff (IP.prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (LinearMap.toContinuousLinearMap (seamFamily hσ (hK₀ q.1) q.2).toLinearMap)) :=
    fun q₀ ↦ by
  -- Near `q₀`, the family is a single Cayley path between two families of pulled back
  -- structures, with parameter `(p, (s, t))`, which is jointly smooth.
  set k := ⌊q₀.2.1.2⌋
  have hc : ContMDiff (IP.prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) ∞
      (fun r : P × (ℝ × ℝ) ↦ 3 * (r.2.2 - k) - 1) :=
    (ContDiff.contMDiff (by fun_prop : ContDiff ℝ ∞
      (fun r : ℝ × ℝ ↦ 3 * (r.2 - k) - 1))).comp contMDiff_snd
  have hreassoc : ContMDiff ((IP.prod 𝓘(ℝ, ℝ × ℝ)).prod I) (IP.prod I) ∞
      (fun r : (P × (ℝ × ℝ)) × M ↦ (r.1.1, r.2)) :=
    (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
  have hpath := (SmoothTwoForm.Compatible.contMDiff_cayleyPath_family
    (K₀ := fun r : P × (ℝ × ℝ) ↦ seamStructure φ (K₀ r.1) k)
    (K₁ := fun r : P × (ℝ × ℝ) ↦ seamStructure φ (K₀ r.1) (k + 1))
    (fun r ↦ compatible_seamStructure hσ (hK₀ r.1) k)
    (fun r ↦ compatible_seamStructure hσ (hK₀ r.1) (k + 1))
    ((contMDiff_seamStructure_family hs k).comp hreassoc)
    ((contMDiff_seamStructure_family hs (k + 1)).comp hreassoc) hc).comp
      (((contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).prodMk
        (contMDiff_snd.comp contMDiff_snd)) :
        ContMDiff (IP.prod (𝓘(ℝ, ℝ × ℝ).prod I)) ((IP.prod 𝓘(ℝ, ℝ × ℝ)).prod I) ∞
          (fun q : P × ((ℝ × ℝ) × M) ↦ ((q.1, q.2.1), q.2.2)))
  refine (hpath q₀).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_snd.comp (continuous_fst.comp continuous_snd)).continuousAt
    |>.preimage_mem_nhds (eventually_seamPath_floor_eq hσ q₀.2.1.2)] with q hq
  rw [seamFamily, SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    LinearMap.toContinuousLinearMap_coe]
  exact congrArg (fun K : SmoothAlmostComplexStructure I M ↦
    TotalSpace.mk' (E →L[ℝ] E) (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
      (K.toEndomorphism q.2.2)) (hq (hK₀ q.1))

end Family

/-- The vertical family is jointly smooth in `((s, t), x)`. -/
theorem contMDiff_seamFamily :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (LinearMap.toContinuousLinearMap (seamFamily hσ hJ₀ p).toLinearMap)) :=
  -- This is the case of the constant family, with parameter in `M` itself.
  (contMDiff_seamFamily_family hσ (IP := I) (K₀ := fun _ : M ↦ J₀) (fun _ ↦ hJ₀)
    (J₀.toEndomorphism.contMDiff.comp contMDiff_snd)).comp (contMDiff_snd.prodMk contMDiff_id)

/-- The vertical family is periodic in `s`. -/
theorem seamFamily_add_fst (p : (ℝ × ℝ) × M) :
    seamFamily hσ hJ₀ (p.1 + (1, 0), p.2) = seamFamily hσ hJ₀ p := by
  simp [seamFamily]

/-- The seam identity `dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`. -/
theorem mfderiv_symm_seamFamily (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    mfderiv I I φ.symm p.2 (seamFamily hσ hJ₀ p v) =
      seamFamily hσ hJ₀ (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v) := by
  have hfloor : ⌊(p.1 + ((0 : ℝ), (1 : ℝ))).2⌋ = ⌊p.1.2⌋ + 1 := by
    simp [Int.floor_add_one]
  -- The piece at time `t + 1` is the pullback by `φ` of the piece at time `t`, so the piece at
  -- time `t` is its pullback by `φ⁻¹`.
  have hpull : (seamPath hσ hJ₀ (⌊p.1.2⌋ + 1) (p.1.2 + 1)).pullback φ.symm =
      seamPath hσ hJ₀ ⌊p.1.2⌋ p.1.2 := by
    rw [seamPath_add_one, ← SmoothAlmostComplexStructure.pullback_trans,
      Diffeomorph.symm_trans_self, SmoothAlmostComplexStructure.pullback_refl]
  rw [seamFamily_apply, seamFamily_apply, hfloor, Prod.snd_add, ← hpull,
    SmoothAlmostComplexStructure.mfderiv_pullback_apply]

include hJ₀ in
/-- Every member of the vertical family is compatible with `σ`. -/
theorem compatible_seamFamily (hσn : σ.IsNondegenerate) (p : (ℝ × ℝ) × M) :
    (hσn.symplecticFormAt p.2).Compatible (seamFamily hσ hJ₀ p) :=
  ((compatible_seamStructure hσ hJ₀ _).compatible_cayleyPath _ _).compatibleAt p.2

/-- On the collar of width `1/3` around the integer time `k`, the vertical family is
`J_k = (φ ^ k)^* J₀`. -/
theorem seamFamily_of_mem_Icc {k : ℤ} {s t : ℝ} (ht : t ∈ Icc ((k : ℝ) - 1 / 3) (k + 1 / 3))
    (x : M) :
    seamFamily hσ hJ₀ ((s, t), x) =
      (seamStructure φ J₀ k).almostComplexStructureAt x := by
  rw [seamFamily]
  rcases le_or_gt (k : ℝ) t with hk | hk
  · rw [Int.floor_eq_iff.2 ⟨hk, by linarith [ht.2]⟩, seamPath_of_le hσ hJ₀ ht.2]
  · have hfl : ⌊t⌋ = k - 1 :=
      Int.floor_eq_iff.2 ⟨by push_cast; linarith [ht.1], by push_cast; linarith⟩
    rw [hfl, seamPath_sub_one hσ hJ₀ ht, seamPath_of_le hσ hJ₀ ht.2]

/-- Around time zero, for `|t| ≤ 1/3`, the vertical family is `J₀`. -/
theorem seamFamily_eq_of_mem_Icc {s t : ℝ} (ht : t ∈ Icc (-(1 / 3) : ℝ) (1 / 3)) (x : M) :
    seamFamily hσ hJ₀ ((s, t), x) = J₀.almostComplexStructureAt x := by
  rw [seamFamily_of_mem_Icc hσ hJ₀ (k := 0) (by simpa using ht), seamStructure_zero]

/-! ### The descended structure -/

variable [T2Space M] [LocallyCompactSpace M]

/-- The block almost complex structure on `(ℝ / ℤ) × Y_φ` descended from the seam-compatible
vertical family built from `J₀`. It sends `∂_s` to the suspension vector field `T` and restricts
to `J₀` on the vertical tangent spaces over the times `t` with `|t| ≤ 1/3`. -/
def seamAlmostComplexStructure :
    SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
      (UnitAddCircle × SmoothMappingTorus φ) :=
  suspensionAlmostComplexStructure φ (contMDiff_seamFamily hσ hJ₀) (seamFamily_add_fst hσ hJ₀)
    (mfderiv_symm_seamFamily hσ hJ₀)

/-- In the coordinates `(s, t, x)`, the descended structure sends `a ∂_s + b ∂_t + v` at
`([s], [t, x])` to `-b ∂_s + a ∂_t + K_((s, t), x) v`. -/
theorem seamAlmostComplexStructure_mk_apply (s t : ℝ) (x : M) (a b : ℝ) (v : TangentSpace I x) :
    seamAlmostComplexStructure hσ hJ₀ ((s : UnitAddCircle), mk φ t x)
        ((Manifold.tangentSpaceProdEquiv _).symm
          (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
      (Manifold.tangentSpaceProdEquiv _).symm
        (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, seamFamily hσ hJ₀ ((s, t), x) v))) :=
  suspensionAlmostComplexStructure_mk φ _ _ _ s t x a b v

/-- On the fibres over the times `t` with `|t| ≤ 1/3`, in the coordinates `(s, t, x)`, the
descended structure sends `a ∂_s + b ∂_t + v` to `-b ∂_s + a ∂_t + J₀ v`. -/
theorem seamAlmostComplexStructure_mk {s t : ℝ} (ht : t ∈ Icc (-(1 / 3) : ℝ) (1 / 3)) (x : M)
    (a b : ℝ) (v : TangentSpace I x) :
    seamAlmostComplexStructure hσ hJ₀ ((s : UnitAddCircle), mk φ t x)
        ((Manifold.tangentSpaceProdEquiv _).symm
          (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
      (Manifold.tangentSpaceProdEquiv _).symm
        (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, J₀ x v))) := by
  rw [seamAlmostComplexStructure_mk_apply, seamFamily_eq_of_mem_Icc hσ hJ₀ ht,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- The descended structure sends `∂_s` to the suspension vector field `T` at every point. -/
theorem seamAlmostComplexStructure_apply_symm_one_zero
    (y : UnitAddCircle × SmoothMappingTorus φ) :
    seamAlmostComplexStructure hσ hJ₀ y ((Manifold.tangentSpaceProdEquiv y).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv y).symm ((0 : ℝ), timeVectorField φ y.2) :=
  suspensionAlmostComplexStructure_apply_symm_one_zero φ _ _ _ y

/-- The descended structure is compatible with the suspension form `Ω = ds ∧ dt + σ_v`. -/
theorem compatible_seamAlmostComplexStructure :
    (suspensionForm φ σ hσ).Compatible (seamAlmostComplexStructure hσ hJ₀) :=
  compatible_suspensionAlmostComplexStructure φ _ _ _ hJ₀.isNondegenerate
    (compatible_seamFamily hσ hJ₀ hJ₀.isNondegenerate)

section Family

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {K₀ : P → SmoothAlmostComplexStructure I M} (hK₀ : ∀ p, σ.Compatible (K₀ p))
  (hs : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
      ((K₀ q.1).toEndomorphism q.2)))

include hs in
/-- For a family `K₀ p` of `σ`-compatible structures depending smoothly on a parameter `p` in a
manifold `P`, the compatible block structures on `(ℝ / ℤ) × Y_φ` built from the `K₀ p` depend
smoothly on the parameter: `(p, y) ↦ (J_p)_y` is a smooth section of the tangent endomorphism
bundle along the projection `P × ((ℝ / ℤ) × Y_φ) → (ℝ / ℤ) × Y_φ`. -/
theorem contMDiff_seamAlmostComplexStructure_family :
    ContMDiff (IP.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I)))
      ((𝓘(ℝ).prod (𝓘(ℝ).prod I)).prod 𝓘(ℝ, (ℝ × (ℝ × E)) →L[ℝ] ℝ × (ℝ × E))) ∞
      (fun r : P × (UnitAddCircle × SmoothMappingTorus φ) ↦
        TotalSpace.mk' ((ℝ × (ℝ × E)) →L[ℝ] ℝ × (ℝ × E))
          (E := fun y : UnitAddCircle × SmoothMappingTorus φ ↦
            TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y →L[ℝ]
              TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y) r.2
          ((seamAlmostComplexStructure hσ (hK₀ r.1)).toEndomorphism r.2)) :=
  contMDiff_suspensionAlmostComplexStructure_family φ
    (K := fun p ↦ seamFamily hσ (hK₀ p)) (contMDiff_seamFamily_family hσ hK₀ hs)
    (fun p ↦ seamFamily_add_fst hσ (hK₀ p)) (fun p ↦ mfderiv_symm_seamFamily hσ (hK₀ p))

end Family

end TauCeti.SmoothMappingTorus
