/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Collar
public import TauCeti.Geometry.Symplectic.Liouville.Graph.Basic
public import TauCeti.Geometry.Symplectic.Liouville.Reeb
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Contact.Flat
import TauCeti.Geometry.Manifold.Flow.Complete

/-!
# The Liouville graph as a level set

Let `M` be a completion of the Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleCompletion`), for the
form `ω` with primitive `α`, Liouville field `Z` (`ι_Z ω = α`) and Liouville flow `ψ`, and let
`ι : S → M` be a smooth injective immersion from a manifold of one dimension less onto the frontier
`∂W`, so that `ι^* α` is a contact form on `S`. For a smooth function `f > 1` on `S`, the
**Liouville graph** `j(s) = ψ_{log f(s)}(ι s)` (`TauCeti.liouvilleGraph`) embeds `S` into the
cylindrical end as a hypersurface `Σ_f` with `j^* α = f ι^* α`
(`TauCeti.mpullback_liouvilleGraph_apply`). Every contact form `f ι^* α` with `f > 1` defining
the same cooriented contact structure as `ι^* α` is thereby realized as the restriction of the
single ambient primitive `α` to a hypersurface.

This file shows that `Σ_f` is a regular level of a function on `M` whose Hamiltonian flow along
`Σ_f` is the Reeb flow of `f ι^* α`, run backwards. Every point `x` of the cylindrical end `M \ W`
is `ψ_t(ι s)` for exactly one `s ∈ S` and one `t > 0`, and the **defining function** of the graph
(`TauCeti.liouvilleGraphFunction`) is

`F(x) = r(x) / f(s) = e^t / f(s)`,

where `r` is the radial coordinate of the end. Its level `1` is exactly `Σ_f`
(`TauCeti.IsLiouvilleCompletion.liouvilleGraphFunction_eq_one_iff`). It is smooth on `M \ W`, since
the Liouville flow map `(t, s) ↦ ψ_t(ι s)` is a local diffeomorphism, injective on `(0, ∞) × S`
with image `M \ W`, so that its inverse is smooth
(`TauCeti.IsLiouvilleCompletion.contMDiffAt_liouvilleGraphFunction`). It is homogeneous of degree
one along the Liouville flow, `F(ψ_τ x) = e^τ F(x)`, so `dF(Z) = F`
(`TauCeti.IsLiouvilleCompletion.mvfderiv_liouvilleGraphFunction_apply`) and `α(X_F) = -F`. On
`Σ_f`, where `F = 1`, the energy-hypersurface identity for `θ = -α`
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback`) therefore gives

`dj(R_{j^* α}) = -X_F`

(`TauCeti.IsLiouvilleCompletion.mfderiv_liouvilleGraph_reebVectorField`). So `j` carries the Reeb
orbits of `f ι^* α`, run backwards, to the orbits of `X_F` on `Σ_f`, and when `S` is compact the
periodic orbits correspond with the same periods
(`TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_liouvilleGraphFunction_iff`).
For constant `f = c` the defining function is `r / c` and this is the correspondence on the levels
of the radial coordinate
(`TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_iff_reebVectorField`).

In the proof of Corollary E of Barraud, Damian, Humilière and Oancea, the closed Reeb orbits of an
arbitrary contact form `f ι^* α` defining the contact structure of `∂W` are obtained as closed
characteristics of the hypersurface `Σ_f`; this file identifies the two kinds of orbits.

## Main definitions

* `TauCeti.liouvilleGraphFunction`: the defining function `r / f` of the Liouville graph of `f`.

## Main results

* `TauCeti.IsLiouvilleCompletion.liouvilleGraphFunction_flowOf`: `F(ψ_t(ι s)) = e^t / f(s)`.
* `TauCeti.IsLiouvilleCompletion.liouvilleGraphFunction_eq_one_iff`: the level `1` of `F` is the
  Liouville graph.
* `TauCeti.IsLiouvilleCompletion.contMDiffAt_liouvilleGraphFunction`: `F` is smooth outside `W`.
* `TauCeti.IsLiouvilleCompletion.mvfderiv_liouvilleGraphFunction_apply`: `dF(Z) = F` outside `W`.
* `TauCeti.IsLiouvilleCompletion.range_mfderiv_liouvilleGraph`: the tangent spaces of the graph
  are the kernels of `dF`.
* `TauCeti.IsLiouvilleCompletion.mfderiv_liouvilleGraph_reebVectorField`: the graph carries the
  Reeb field of `j^* α` to `-X_F`.
* `TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_liouvilleGraphFunction_iff`:
  the periods of `X_F` on the graph are the Reeb periods of `j^* α = f ι^* α`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary E and its proof (the graph of a
  contact form in the symplectization of a hypersurface of restricted contact type).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their characteristic line fields).
-/

public section

open Function Module Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {S : Type*}
  {Z : (x : M) → TangentSpace I x} {W : Set M} {ι : S → M} {f : S → ℝ} {x : M}

variable (Z W ι f) in
/-- The **defining function of the Liouville graph** of `f` over `ι : S → M`, on a completion of
the Liouville domain `W` whose boundary `ι` parametrizes: a point `x = ψ_t(ι s)` of the
cylindrical end, reached from the boundary point `ι s` by the Liouville flow `ψ` in time `t > 0`,
goes to `r(x) / f(s) = e^t / f(s)`, where `r` is the radial coordinate. Its level `1` is the
Liouville graph `s ↦ ψ_{log f(s)}(ι s)` when `f > 1`
(`TauCeti.IsLiouvilleCompletion.liouvilleGraphFunction_eq_one_iff`). On `W` itself, where `r = 1`,
its values are not meaningful. -/
noncomputable def liouvilleGraphFunction [Nonempty S] (x : M) : ℝ :=
  liouvilleRadialCoordinate Z W x /
    f (invFunOn (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) (Ioi 0 ×ˢ univ) x).2

/-- The defining function of the Liouville graph is the radial coordinate divided by `f` at the
`S`-coordinate of the inverse of the Liouville flow map `(t, s) ↦ ψ_t(ι s)` on `(0, ∞) × S`. -/
theorem liouvilleGraphFunction_def [Nonempty S] (x : M) :
    liouvilleGraphFunction Z W ι f x = liouvilleRadialCoordinate Z W x /
      f (invFunOn (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) (Ioi 0 ×ˢ univ) x).2 :=
  (rfl)

namespace IsLiouvilleCompletion

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1}

/-- The Liouville flow out of an injective parametrization of the boundary is injective on
`(0, ∞) × S`. -/
private theorem injOn_flowOf_comp (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hιW : ∀ s, ι s ∈ frontier W) (hinj : Injective ι) :
    InjOn (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) (Ioi 0 ×ˢ univ) := by
  rintro ⟨t, s⟩ ⟨ht, -⟩ ⟨t', s'⟩ ⟨ht', -⟩ hq
  have := (h.bijOn_flowOf_Ioi_prod_frontier hZ).injOn (x₁ := (t, ι s)) (x₂ := (t', ι s'))
    ⟨ht, hιW s⟩ ⟨ht', hιW s'⟩ hq
  simp only [Prod.mk.injEq] at this ⊢
  exact ⟨this.1, hinj this.2⟩

/-- The Liouville flow out of a parametrization of the boundary maps `(0, ∞) × S` onto the
complement of the Liouville domain. -/
private theorem image_flowOf_comp (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hιW : ∀ s, ι s ∈ frontier W)
    (hWι : frontier W ⊆ range ι) :
    (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) '' (Ioi 0 ×ˢ univ) = Wᶜ := by
  rw [← (h.bijOn_flowOf_Ioi_prod_frontier hZ).image_eq]
  ext x
  constructor
  · rintro ⟨⟨t, s⟩, ⟨ht, -⟩, rfl⟩
    exact ⟨(t, ι s), ⟨ht, hιW s⟩, rfl⟩
  · rintro ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
    obtain ⟨s, rfl⟩ := hWι hy
    exact ⟨(t, s), ⟨ht, mem_univ s⟩, rfl⟩

/-- **The defining function of the Liouville graph on the cylindrical end.** At the point
`ψ_t(ι s)`, `t > 0`, the defining function of the Liouville graph of `f` is `e^t / f(s)`. -/
theorem liouvilleGraphFunction_flowOf [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hιW : ∀ s, ι s ∈ frontier W) (hinj : Injective ι)
    {t : ℝ} (ht : 0 < t) (s : S) :
    liouvilleGraphFunction Z W ι f (flowOf Z t (ι s)) = Real.exp t / f s := by
  have hp := (h.injOn_flowOf_comp hZ hιW hinj).leftInvOn_invFunOn
    (show (t, s) ∈ Ioi 0 ×ˢ (univ : Set S) from ⟨ht, mem_univ s⟩)
  rw [liouvilleGraphFunction_def, h.liouvilleRadialCoordinate_flowOf hZ (hιW s) ht.le]
  simp only at hp
  rw [hp]

/-- **The Liouville graph lies on the level `1`** of its defining function: at a point `s` with
`f s > 1`, the graph point `ψ_{log f(s)}(ι s)` has value `e^{log f(s)} / f(s) = 1`. -/
theorem liouvilleGraphFunction_liouvilleGraph [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hιW : ∀ s, ι s ∈ frontier W) (hinj : Injective ι)
    {s : S} (hfs : 1 < f s) :
    liouvilleGraphFunction Z W ι f (liouvilleGraph Z ι f s) = 1 := by
  rw [liouvilleGraph_apply, h.liouvilleGraphFunction_flowOf hZ hιW hinj (Real.log_pos hfs),
    Real.exp_log (one_pos.trans hfs), div_self (one_pos.trans hfs).ne']

/-- On the Liouville domain, where the radial coordinate is `1`, the defining function of the
Liouville graph of a function `f > 1` is below `1`. -/
theorem liouvilleGraphFunction_lt_one_of_mem [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hf : ∀ s, 1 < f s) (hx : x ∈ W) :
    liouvilleGraphFunction Z W ι f x < 1 := by
  rw [liouvilleGraphFunction_def, (h.liouvilleRadialCoordinate_eq_one_iff hZ).2 hx]
  exact (div_lt_one (one_pos.trans (hf _))).2 (hf _)

/-- **The level `1` of the defining function is the Liouville graph.** Let `ι` be an injective
parametrization of the boundary of the Liouville domain and `f > 1`. A point lies on the level `1`
of the defining function of the Liouville graph of `f` exactly when it is a point
`ψ_{log f(s)}(ι s)` of the graph. -/
theorem liouvilleGraphFunction_eq_one_iff [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hιW : ∀ s, ι s ∈ frontier W) (hinj : Injective ι)
    (hWι : frontier W ⊆ range ι) (hf : ∀ s, 1 < f s) :
    liouvilleGraphFunction Z W ι f x = 1 ↔ x ∈ range (liouvilleGraph Z ι f) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hxW : x ∈ Wᶜ := fun hxW ↦ (h.liouvilleGraphFunction_lt_one_of_mem hZ hf hxW).ne hx
    rw [← h.image_flowOf_comp hZ hιW hWι] at hxW
    obtain ⟨⟨t, s⟩, ⟨ht, -⟩, rfl⟩ := hxW
    have hfs : 0 < f s := one_pos.trans (hf s)
    rw [h.liouvilleGraphFunction_flowOf hZ hιW hinj ht, div_eq_one_iff_eq hfs.ne'] at hx
    exact ⟨s, by rw [liouvilleGraph_apply, ← hx, Real.log_exp]⟩
  · rintro ⟨s, rfl⟩
    exact h.liouvilleGraphFunction_liouvilleGraph hZ hιW hinj (hf s)

/-- **The defining function is homogeneous along the Liouville flow.** On the cylindrical end,
the Liouville flow multiplies the defining function of the Liouville graph by `e^τ`:
`F(ψ_τ x) = e^τ F(x)` whenever `x` and `ψ_τ x` both lie outside the Liouville domain. -/
theorem liouvilleGraphFunction_flowOf_eq_exp_mul [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hιW : ∀ s, ι s ∈ frontier W) (hinj : Injective ι)
    (hWι : frontier W ⊆ range ι) (hx : x ∉ W) {τ : ℝ} (hτ : flowOf Z τ x ∉ W) :
    liouvilleGraphFunction Z W ι f (flowOf Z τ x) =
      Real.exp τ * liouvilleGraphFunction Z W ι f x := by
  have hxW : x ∈ Wᶜ := hx
  rw [← h.image_flowOf_comp hZ hιW hWι] at hxW
  obtain ⟨⟨t, s⟩, ⟨ht, -⟩, rfl⟩ := hxW
  rw [h.flowOf_flowOf hZ] at hτ ⊢
  have hτt : 0 < τ + t :=
    not_le.1 fun hle ↦ hτ ((h.flowOf_mem_iff_of_mem_frontier hZ (hιW s)).2 hle)
  rw [h.liouvilleGraphFunction_flowOf hZ hιW hinj hτt,
    h.liouvilleGraphFunction_flowOf hZ hιW hinj ht, Real.exp_add, mul_div_assoc]

section Smooth

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S]
  [ChartedSpace H' S] [IsManifold J (⊤ : ℕ∞) S]

/-- **The defining function of the Liouville graph is smooth on the cylindrical end.** Let
`ι : S → M` be a smooth injective immersion onto the frontier of the Liouville domain, from a
manifold of one dimension less, and let `f` be smooth and nowhere zero. Then the defining function
of the Liouville graph of `f` is smooth at every point outside the Liouville domain: there the
Liouville flow map `(t, s) ↦ ψ_t(ι s)` has a smooth inverse. -/
theorem contMDiffAt_liouvilleGraphFunction [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W) (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hinj : Injective ι) (hWι : frontier W ⊆ range ι)
    (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (hf₀ : ∀ s, f s ≠ 0) (hx : x ∉ W) :
    ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) (liouvilleGraphFunction Z W ι f) x := by
  have hZα : (mextDeriv α.val).interior Z = α.val := by rw [h.mextDeriv_eq]; exact hZ
  -- The Liouville flow map is a local diffeomorphism, injective on `(0, ∞) × S` with image
  -- `Wᶜ`, so its inverse there is smooth.
  have hloc : IsLocalDiffeomorphOn (𝓘(ℝ).prod J) I (⊤ : ℕ∞)
      (fun q : ℝ × S ↦ flowOf Z q.1 (ι q.2)) (Ioi 0 ×ˢ univ) := fun q ↦
    isLocalDiffeomorphAt_flowOf_comp (h.contMDiff_of_interior_eq hZ) hι hdim hZα
      (h.isContactForm_mpullback hZ hι hιW hιs hdim)
      ((h.isCompleteVectorField hZ).mem_flowDomain _ _)
  have hp := hloc.contMDiffOn_invFunOn (isOpen_Ioi.prod isOpen_univ)
    (h.injOn_flowOf_comp hZ hιW hinj)
  rw [h.image_flowOf_comp hZ hιW hWι] at hp
  have hpx := hp.contMDiffAt (h.isClosed.isOpen_compl.mem_nhds hx)
  exact (h.contMDiffAt_liouvilleRadialCoordinate hZ hx).div₀
    ((hf _).comp x (contMDiffAt_snd.comp x hpx)) (hf₀ _)

/-- **The Liouville field differentiates the defining function to itself.** Outside the Liouville
domain, `dF(Z) = F` for the defining function `F` of the Liouville graph of `f`: it is the
infinitesimal form of `F(ψ_τ x) = e^τ F(x)`. -/
theorem mvfderiv_liouvilleGraphFunction_apply [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W) (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hinj : Injective ι) (hWι : frontier W ⊆ range ι)
    (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (hf₀ : ∀ s, f s ≠ 0) (hx : x ∉ W) :
    mvfderiv I (liouvilleGraphFunction Z W ι f) x (Z x) = liouvilleGraphFunction Z W ι f x := by
  set F := liouvilleGraphFunction Z W ι f
  have hF : MDifferentiableAt I 𝓘(ℝ) F (flowOf Z 0 x) := by
    rw [flowOf_zero Z]
    exact (h.contMDiffAt_liouvilleGraphFunction hZ hι hιW hιs hdim hinj hWι hf hf₀
      hx).mdifferentiableAt (by simp)
  have hcurve := hasDerivAt_comp_flowOf ((h.contMDiff_of_interior_eq hZ).of_le (by simp))
    ((h.isCompleteVectorField hZ).mem_flowDomain 0 x) hF
  rw [flowOf_zero Z] at hcurve
  -- Along the trajectory `x = ψ_t(ι s)`, the flow stays outside `W` for times `τ > -t`.
  have hxW : x ∈ Wᶜ := hx
  rw [← h.image_flowOf_comp hZ hιW hWι] at hxW
  obtain ⟨⟨t, s⟩, ⟨ht, -⟩, hts⟩ := hxW
  have heq : (F ∘ fun τ ↦ flowOf Z τ x) =ᶠ[𝓝 0] fun τ ↦ Real.exp τ * F x := by
    filter_upwards [Ioi_mem_nhds (neg_lt_zero.2 (mem_Ioi.1 ht))] with τ hτ
    refine h.liouvilleGraphFunction_flowOf_eq_exp_mul hZ hιW hinj hWι hx ?_
    rw [← hts, h.flowOf_flowOf hZ, h.flowOf_mem_iff_of_mem_frontier hZ (hιW s), not_le]
    linarith [mem_Ioi.1 hτ]
  refine hcurve.unique (HasDerivAt.congr_of_eventuallyEq ?_ heq)
  simpa using (Real.hasDerivAt_exp 0).mul_const (F x)

/-- **The primitive on the field of the defining function.** Outside the Liouville domain, the
primitive takes the value `-F` on the Hamiltonian vector field `X_F` of the defining function `F`
of the Liouville graph: `α(X_F) = ω(Z, X_F) = -dF(Z) = -F`. -/
theorem apply_hamiltonianVectorField_liouvilleGraphFunction [Nonempty S]
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hinj : Injective ι) (hWι : frontier W ⊆ range ι) (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f)
    (hf₀ : ∀ s, f s ≠ 0) (hx : x ∉ W) :
    α.val x ![ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f) x] =
      -liouvilleGraphFunction Z W ι f x := by
  have hα : α.val x ![ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f) x] =
      SmoothBundleForm.eval₂ ω x (Z x)
        (ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f) x) := by
    rw [← hZ, RoughForm.interior_apply, SmoothBundleForm.eval₂_apply]
  rw [hα, SmoothBundleForm.eval₂_swap, h.isNondegenerate.eval₂_hamiltonianVectorField,
    h.mvfderiv_liouvilleGraphFunction_apply hZ hι hιW hιs hdim hinj hWι hf hf₀ hx]

/-- **The Liouville graph is a level of its defining function, infinitesimally.** Let `ι` be a
smooth injective immersion onto the frontier of the Liouville domain, from a manifold of one
dimension less, and `f > 1` smooth. The image of the differential of the Liouville graph `j` of
`f` at `s` is the kernel of the differential of its defining function at `j(s)`. -/
theorem range_mfderiv_liouvilleGraph [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W) (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hinj : Injective ι) (hWι : frontier W ⊆ range ι)
    (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (hf1 : ∀ s, 1 < f s) (s : S) :
    (mfderiv J I (liouvilleGraph Z ι f) s).range =
      (mvfderiv I (liouvilleGraphFunction Z W ι f) (liouvilleGraph Z ι f s)).ker := by
  set F := liouvilleGraphFunction Z W ι f
  set j := liouvilleGraph Z ι f
  have hf₀ : ∀ s, f s ≠ 0 := fun s ↦ (one_pos.trans (hf1 s)).ne'
  have hZs := h.contMDiff_of_interior_eq hZ
  have hc := h.isCompleteVectorField hZ
  have hx : j s ∉ W := h.liouvilleGraph_notMem hZ (hc.mem_flowDomain _ _) (hιW s).2 (hf1 s)
  have hFx : MDifferentiableAt I 𝓘(ℝ) F (j s) :=
    (h.contMDiffAt_liouvilleGraphFunction hZ hι hιW hιs hdim hinj hWι hf hf₀
      hx).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt J I j s :=
    (contMDiff_liouvilleGraph le_top hZs hc hι hf hf₀ s).mdifferentiableAt (by simp)
  -- `F ∘ j` is the constant `1`, so the image of the differential lies in `ker dF`.
  have hle : (mfderiv J I j s).range ≤ (mvfderiv I F (j s)).ker := by
    rintro _ ⟨w, rfl⟩
    have hconst : F ∘ j = fun _ ↦ 1 :=
      funext fun s' ↦ h.liouvilleGraphFunction_liouvilleGraph hZ hιW hinj (hf1 s')
    have hcomp := mfderiv_comp s hFx hg
    rw [hconst, mfderiv_const] at hcomp
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mvfderiv_apply_eq_mfderiv_apply]
    exact (congrArg (· w) hcomp).symm
  -- Both sides have dimension `dim E - 1`: `dF(Z) = F = 1` does not vanish.
  have hne : (mvfderiv I F (j s) : TangentSpace I (j s) →ₗ[ℝ] ℝ) ≠ 0 := fun h0 ↦ by
    have hZx := h.mvfderiv_liouvilleGraphFunction_apply hZ hι hιW hιs hdim hinj hWι hf hf₀ hx
    rw [← ContinuousLinearMap.coe_coe, h0, LinearMap.zero_apply,
      h.liouvilleGraphFunction_liouvilleGraph hZ hιW hinj (hf1 s)] at hZx
    exact zero_ne_one hZx
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [LinearMap.finrank_range_of_inj (injective_mfderiv_liouvilleGraph (hZs.of_le (by simp)) hc
    ((hι s).mdifferentiableAt (by simp)) ((hf s).mdifferentiableAt (by simp)) (hf₀ s) (hιs s)
    (h.isTransverseAlong hZ (hι.mdifferentiable (by simp)) hιW))]
  exact Nat.add_right_cancel (hdim.trans hker.symm)

omit [FiniteDimensional ℝ E'] [J.Boundaryless] in
/-- The restriction `j^* α` of the primitive to the Liouville graph `j` is a contact form. -/
private theorem isContactForm_mpullback_liouvilleGraph (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W) (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f)
    (hf₀ : ∀ s, f s ≠ 0) :
    (SmoothForm.mpullback (liouvilleGraph Z ι f) (contMDiff_liouvilleGraph le_top
      (h.contMDiff_of_interior_eq hZ) (h.isCompleteVectorField hZ) hι hf hf₀) α).IsContactForm := by
  have hZs := h.contMDiff_of_interior_eq hZ
  have hc := h.isCompleteVectorField hZ
  exact (h.isRestrictedContactType_liouvilleGraph hZ hc (hι.mdifferentiable (by simp)) hιs hιW
    (hf.mdifferentiable (by simp)) hf₀).isContactType.isContactForm_mpullback h.isNondegenerate _
    (fun s ↦ injective_mfderiv_liouvilleGraph (hZs.of_le (by simp)) hc
      ((hι s).mdifferentiableAt (by simp)) ((hf s).mdifferentiableAt (by simp)) (hf₀ s) (hιs s)
      (h.isTransverseAlong hZ (hι.mdifferentiable (by simp)) hιW)) hdim

/-- **The Reeb field of the Liouville graph is minus the field of its defining function.** Let `ι`
be a smooth injective immersion onto the frontier of the Liouville domain, from a manifold of one
dimension less, and `f > 1` smooth. The differential of the Liouville graph `j` of `f` sends the
Reeb vector field of the contact form `j^* α`, which is `f ι^* α`, to `-X_F` at `j(s)`, where `F`
is the defining function of the graph. -/
theorem mfderiv_liouvilleGraph_reebVectorField [Nonempty S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W) (hιs : ∀ s, Injective (mfderiv J I ι s))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hinj : Injective ι) (hWι : frontier W ⊆ range ι)
    (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f) (hf1 : ∀ s, 1 < f s) (s : S) :
    mfderiv J I (liouvilleGraph Z ι f) s
        ((SmoothForm.mpullback (liouvilleGraph Z ι f) (contMDiff_liouvilleGraph le_top
          (h.contMDiff_of_interior_eq hZ) (h.isCompleteVectorField hZ) hι hf
          fun s ↦ (one_pos.trans (hf1 s)).ne') α).reebVectorField s) =
      -ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f) (liouvilleGraph Z ι f s) := by
  have hf₀ : ∀ s, f s ≠ 0 := fun s ↦ (one_pos.trans (hf1 s)).ne'
  have hj := contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ)
    (h.isCompleteVectorField hZ) hι hf hf₀
  have hα₀ := h.isContactForm_mpullback_liouvilleGraph hZ hι hιW hιs hdim hf hf₀
  have hx : liouvilleGraph Z ι f s ∉ W := h.liouvilleGraph_notMem hZ
    ((h.isCompleteVectorField hZ).mem_flowDomain _ _) (hιW s).2 (hf1 s)
  -- Apply the energy-hypersurface identity to `θ = -α`, for which `θ(X_F) = F = 1`.
  have hθ : (-α).val (liouvilleGraph Z ι f s)
      ![ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f) (liouvilleGraph Z ι f s)] =
        1 := by
    rw [Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
      h.apply_hamiltonianVectorField_liouvilleGraphFunction hZ hι hιW hιs hdim hinj hWι hf hf₀ hx,
      neg_neg, h.liouvilleGraphFunction_liouvilleGraph hZ hιW hinj (hf1 s)]
  have key := h.isNondegenerate.mfderiv_reebVectorField_mpullback hj
    (by rw [map_neg, SmoothForm.isContactForm_neg_iff]; exact hα₀)
    (K := liouvilleGraphFunction Z W ι f) (s := s)
    (by rw [Submodule.coe_neg, mextDeriv_neg, h.mextDeriv_eq, Pi.neg_apply])
    (h.range_mfderiv_liouvilleGraph hZ hι hιW hιs hdim hinj hWι hf hf1 s)
  rw [hθ, inv_one, one_smul, map_neg, hα₀.reebVectorField_neg, map_neg] at key
  exact neg_eq_iff_eq_neg.1 key

/-- **The Liouville graph carries reversed Reeb orbits to orbits of its defining function.** Let
`ι` be a smooth injective immersion onto the frontier of the Liouville domain, from a manifold of
one dimension less, `f > 1` smooth, and `γ` an integral curve of the Reeb field of the contact
form `j^* α = f ι^* α` of the Liouville graph `j` of `f`. Then `τ ↦ j(γ(-τ))`, on the level `1` of
the defining function `F` of the graph, is an integral curve of `X_F`. -/
theorem isMIntegralCurve_liouvilleGraph_reebVectorField [Nonempty S]
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hinj : Injective ι) (hWι : frontier W ⊆ range ι) (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f)
    (hf1 : ∀ s, 1 < f s) {γ : ℝ → S}
    (hγ : IsMIntegralCurve γ (SmoothForm.mpullback (liouvilleGraph Z ι f)
      (contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ) (h.isCompleteVectorField hZ)
        hι hf fun s ↦ (one_pos.trans (hf1 s)).ne') α).reebVectorField) :
    IsMIntegralCurve (fun τ ↦ liouvilleGraph Z ι f (γ (-τ)))
      (ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f)) := by
  have hγ' := hγ.comp_mul (-1)
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ' ⊢
  have hmap := hγ'.map_of_mfderiv_eq (f := liouvilleGraph Z ι f)
    (fun τ _ ↦ (contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ)
      (h.isCompleteVectorField hZ) hι hf (fun s ↦ (one_pos.trans (hf1 s)).ne') _).mdifferentiableAt
      (by simp))
    (fun τ _ ↦ by
      rw [Pi.smul_apply, map_smul, h.mfderiv_liouvilleGraph_reebVectorField hZ hι hιW hιs hdim hinj
        hWι hf hf1, neg_one_smul, neg_neg, comp_apply])
  simpa [comp_def] using hmap

/-- **The orbits of the defining function on the Liouville graph are determined by their initial
point.** Let `ι` be a smooth injective immersion from a compact manifold of one dimension less
onto the frontier of the Liouville domain, and `f > 1` smooth. Two integral curves of `X_F` on the
level `1` of the defining function `F` of the Liouville graph of `f` which agree at time `0` are
equal. -/
theorem eq_of_isMIntegralCurve_hamiltonianVectorField_liouvilleGraphFunction [CompactSpace S]
    [Nonempty S] (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hinj : Injective ι) (hWι : frontier W ⊆ range ι) (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f)
    (hf1 : ∀ s, 1 < f s) {δ δ' : ℝ → M}
    (hδ : IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f)))
    (hδ' : IsMIntegralCurve δ' (ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f)))
    (hδc : ∀ τ, liouvilleGraphFunction Z W ι f (δ τ) = 1)
    (hδ'c : ∀ τ, liouvilleGraphFunction Z W ι f (δ' τ) = 1) (h0 : δ 0 = δ' 0) : δ = δ' := by
  set F := liouvilleGraphFunction Z W ι f
  have hf₀ : ∀ s, f s ≠ 0 := fun s ↦ (one_pos.trans (hf1 s)).ne'
  have hr : Continuous (liouvilleRadialCoordinate Z W) := h.continuous_liouvilleRadialCoordinate hZ
  -- On the compact `S`, `f` is bounded below by its minimum `m > 1`, and `r ≥ m` on the level.
  obtain ⟨s₀, -, hs₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuous.continuousOn
  have hlev : ∀ y, F y = 1 → f s₀ ≤ liouvilleRadialCoordinate Z W y := fun y hy ↦ by
    obtain ⟨s, rfl⟩ := (h.liouvilleGraphFunction_eq_one_iff hZ hιW hinj hWι hf1).1 hy
    exact (hs₀ (mem_univ s)).trans
      (h.liouvilleRadialCoordinate_liouvilleGraph hZ (hιW s) (hf1 s).le).ge
  obtain ⟨ε, hε, hεc⟩ : ∃ ε : ℝ, 0 < ε ∧ 1 + 2 * ε < f s₀ :=
    ⟨(f s₀ - 1) / 4, div_pos (sub_pos.2 (hf1 s₀)) four_pos, by linarith [hf1 s₀]⟩
  -- A smooth `φ` with `φ(u) = 0` for `u ≤ 1 + ε` and `φ(u) = 1` for `u ≥ 1 + 2ε`.
  set φ : ℝ → ℝ := fun u ↦ Real.smoothTransition ((u - (1 + ε)) / ε)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε)
  have hφ0 : ∀ u ≤ 1 + ε, φ u = 0 := fun u hu ↦
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)
  have hφ1 : ∀ u, 1 + 2 * ε ≤ u → φ u = 1 := fun u hu ↦
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith)
  -- `G = (φ ∘ r) F`, for the radial coordinate `r`, is smooth: it vanishes near the Liouville
  -- domain, where `r = 1`.
  set G : M → ℝ := fun y ↦ φ (liouvilleRadialCoordinate Z W y) * F y
  have hG : ContMDiff I 𝓘(ℝ) (⊤ : ℕ∞) G := fun y ↦ by
    by_cases hy : y ∈ W
    · have hry : liouvilleRadialCoordinate Z W y < 1 + ε := by
        rw [(h.liouvilleRadialCoordinate_eq_one_iff hZ).2 hy]
        linarith
      refine contMDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt hr continuous_const).mem_nhds hry] with z hz
      simp [G, hφ0 _ hz.le]
    · exact (hφ.contDiffAt.comp_contMDiffAt (h.contMDiffAt_liouvilleRadialCoordinate hZ hy)).mul
        (h.contMDiffAt_liouvilleGraphFunction hZ hι hιW hιs hdim hinj hWι hf hf₀ hy)
  -- Near the level `1`, `G = F`, so the two Hamiltonian fields agree there.
  have hXG : ∀ y, F y = 1 → ω.hamiltonianVectorField F y = ω.hamiltonianVectorField G y :=
    fun y hy ↦ Filter.EventuallyEq.hamiltonianVectorField_eq ω <| by
      filter_upwards [(isOpen_lt continuous_const hr).mem_nhds (hεc.trans_le (hlev y hy))]
        with z hz
      simp [G, hφ1 _ hz.le]
  have hv : ContMDiff I I.tangent 1 (T% (ω.hamiltonianVectorField G)) :=
    h.isNondegenerate.contMDiff_hamiltonianVectorField (by simp) (hG.of_le (by simp))
  exact isMIntegralCurve_eq_of_contMDiff (fun _ ↦ BoundarylessManifold.isInteriorPoint) hv
    ((isMIntegralCurve_congr_vectorField fun τ ↦ hXG _ (hδc τ)).1 hδ)
    ((isMIntegralCurve_congr_vectorField fun τ ↦ hXG _ (hδ'c τ)).1 hδ') h0

/-- **The periods of the defining function on the Liouville graph are the Reeb periods of
`f ι^* α`.** Let `ι : S → M` be a smooth injective immersion from a compact boundaryless manifold
of one dimension less onto the frontier of the Liouville domain, and `f > 1` smooth. The
Hamiltonian vector field `X_F` of the defining function `F` of the Liouville graph `j` of `f` has
a `T`-periodic integral curve on the level `1` exactly when the Reeb field of the contact form
`j^* α = f ι^* α` has a `T`-periodic integral curve: `j` carries the reversed Reeb orbits onto the
orbits of `X_F` on the graph. -/
theorem exists_periodic_hamiltonianVectorField_liouvilleGraphFunction_iff [CompactSpace S]
    [Nonempty S] (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hinj : Injective ι) (hWι : frontier W ⊆ range ι) (hf : ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f)
    (hf1 : ∀ s, 1 < f s) {T : ℝ} :
    (∃ δ : ℝ → M, IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleGraphFunction Z W ι f)) ∧
        Periodic δ T ∧ ∀ τ, liouvilleGraphFunction Z W ι f (δ τ) = 1) ↔
      ∃ γ : ℝ → S, IsMIntegralCurve γ (SmoothForm.mpullback (liouvilleGraph Z ι f)
        (contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ)
          (h.isCompleteVectorField hZ) hι hf fun s ↦ (one_pos.trans (hf1 s)).ne')
          α).reebVectorField ∧
        Periodic γ T := by
  have : T2Space S := T2Space.of_injective_continuous hinj hι.continuous
  have hf₀ : ∀ s, f s ≠ 0 := fun s ↦ (one_pos.trans (hf1 s)).ne'
  have hlevel (γ : ℝ → S) (τ : ℝ) :
      liouvilleGraphFunction Z W ι f (liouvilleGraph Z ι f (γ (-τ))) = 1 :=
    h.liouvilleGraphFunction_liouvilleGraph hZ hιW hinj (hf1 _)
  constructor
  · rintro ⟨δ, hδ, hδT, hδc⟩
    -- The orbit of `X_F` through `δ 0` starts at a graph point `j s₀`.
    obtain ⟨s₀, hs₀⟩ := (h.liouvilleGraphFunction_eq_one_iff hZ hιW hinj hWι hf1).1 (hδc 0)
    -- The Reeb field of the compact `S` is complete; follow its orbit through `s₀`.
    have hR : ContMDiff J J.tangent 1 (T% (SmoothForm.mpullback (liouvilleGraph Z ι f)
        (contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ)
          (h.isCompleteVectorField hZ) hι hf hf₀) α).reebVectorField) :=
      (h.isContactForm_mpullback_liouvilleGraph hZ hι hιW hιs hdim hf
        hf₀).contMDiff_reebVectorField.of_le (by simp)
    set γ := fun τ ↦ globalFlow _ hR (isCompleteVectorField_of_compactSpace hR) τ s₀
    have hγ : IsMIntegralCurve γ (SmoothForm.mpullback (liouvilleGraph Z ι f)
        (contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ)
          (h.isCompleteVectorField hZ) hι hf hf₀) α).reebVectorField :=
      isMIntegralCurve_globalFlow _ _ s₀
    have heq : (fun τ ↦ liouvilleGraph Z ι f (γ (-τ))) = δ :=
      h.eq_of_isMIntegralCurve_hamiltonianVectorField_liouvilleGraphFunction hZ hι hιW hιs hdim
        hinj hWι hf hf1
        (h.isMIntegralCurve_liouvilleGraph_reebVectorField hZ hι hιW hιs hdim hinj hWι hf hf1 hγ)
        hδ (hlevel γ) hδc (by simp only [neg_zero, γ, Flow.map_zero_apply, hs₀])
    -- The graph is injective, so the periodicity of `δ` passes to `γ`.
    have hinjg : Injective (liouvilleGraph Z ι f) :=
      h.injective_liouvilleGraph hZ (h.isCompleteVectorField hZ) hinj hιW
    refine ⟨γ, hγ, fun τ ↦ hinjg ?_⟩
    have e₁ := congrFun heq (-(τ + T))
    have e₂ := congrFun heq (-τ)
    simp only [neg_neg] at e₁ e₂
    rw [e₁, e₂, ← hδT (-(τ + T)), neg_add, neg_add_cancel_right]
  · rintro ⟨γ, hγ, hγT⟩
    refine ⟨fun τ ↦ liouvilleGraph Z ι f (γ (-τ)),
      h.isMIntegralCurve_liouvilleGraph_reebVectorField hZ hι hιW hιs hdim hinj hWι hf hf1 hγ,
      fun τ ↦ ?_, hlevel γ⟩
    simp only [neg_add, ← sub_eq_add_neg, hγT.sub_eq]

end Smooth

end IsLiouvilleCompletion

end TauCeti
