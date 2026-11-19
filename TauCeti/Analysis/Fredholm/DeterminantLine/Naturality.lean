/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# Naturality of Fredholm determinant lines and of their orientations

A commuting square `S ∘ e₁ = e₂ ∘ T` of operators, with isomorphisms `e₁` of the sources and `e₂`
of the targets, induces an isomorphism of determinant lines `det T ≃ det S`
(`LinearMap.detLineCongr`). This file shows that these isomorphisms are compatible with the
structure through which the determinant lines of Fredholm operators are compared and oriented:
stabilizations, kernel charts, coherent families and orientation transport. Orientations of
determinant lines can therefore be moved between conjugate families of operators, for instance
between the expressions of a family of operators in two trivializations of a bundle, or along a
rescaling of the target.

The underlying linear algebra is in the files where stabilizations and kernel charts are defined:
the normalized stabilization isomorphisms are natural
(`ContinuousLinearMap.detLineStabilizationEquiv_congr`), and so are the kernel charts
(`ContinuousLinearMap.detLineChartEquiv_detLineCongr_of_comp_eq`), and over `ℝ` a kernel chart
whose stabilizer and coordinate move continuously is, nearby, a positive multiple of the chart
with the data frozen (`ContinuousLinearMap.eventually_detLineChartEquiv_eq_smul`).

* **Coherence and transport.** Let `S x ∘ e₁ x = e₂ x ∘ T x` for families of isomorphisms which
  are continuous in the operator norm. The transport along these squares of a family coherent for
  `T` is coherent for `S` (`TauCeti.IsDetLineCoherentWithinAt.detLineCongr`,
  `TauCeti.IsDetLineCoherentOn.detLineCongr`): read on `T x`, a fixed kernel chart of `S x` has the
  moving stabilizer `(e₂ x)⁻¹ ∘ D₂` and coordinate `q ∘ (e₁ x × 1)`. Hence orientation transport
  along `S` is orientation transport along `T`, conjugated by the transports along the squares at
  the two ends (`TauCeti.detLineOrientationTransport_map_detLineCongr`).
* **Isomorphisms of the target.** For a Fredholm operator `T₀` and a path `A` of isomorphisms of
  its target, orientation transport along `t ↦ A t ∘ T₀` is the isomorphism of determinant lines
  induced by `A b ∘ (A a)⁻¹`, whatever the path (`TauCeti.detLineOrientationTransport_comp_left`).
  For example, the positive block rescaling `(f, η) ↦ (2 f, η / √2)` of the target, joined to the
  identity through positive block rescalings, carries the orientations of the determinant line of
  `(-d^*, √2 d⁺)` to those of `(-2 d^*, d⁺)` by the isomorphism of determinant lines it induces.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Module TensorProduct

namespace TauCeti

open Filter Set Topology ContinuousLinearMap

section Coherent

variable {E F E' F' X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F'] [TopologicalSpace X]
  {T : X → E →L[ℝ] F} {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} {x₀ : X}

variable {S : X → E' →L[ℝ] F'} {e₁ : X → E ≃L[ℝ] E'} {e₂ : X → F ≃L[ℝ] F'}

/-- **Naturality of coherence.** Let `T` be a family of operators continuous within `s` at `x₀`,
with `T x₀` Fredholm, and let `S x ∘ e₁ x = e₂ x ∘ T x` for families of isomorphisms `e₁` of the
sources and `e₂` of the targets, continuous within `s` at `x₀`. If `v` is coherent for `T` within
`s` at `x₀`, then its transport along the squares, `LinearMap.detLineCongr`, is coherent for
`S`. -/
theorem IsDetLineCoherentWithinAt.detLineCongr (hv : IsDetLineCoherentWithinAt T v s x₀)
    (hT : ContinuousWithinAt T s x₀) (hF : IsFredholm (T x₀))
    (he₁ : ContinuousWithinAt (fun x ↦ (e₁ x : E →L[ℝ] E')) s x₀)
    (he₂ : ContinuousWithinAt (fun x ↦ (e₂ x : F →L[ℝ] F')) s x₀)
    (h : ∀ x, (S x : E' →ₗ[ℝ] F') ∘ₗ (e₁ x).toLinearEquiv.toLinearMap =
      (e₂ x).toLinearEquiv.toLinearMap ∘ₗ (T x : E →ₗ[ℝ] F)) :
    IsDetLineCoherentWithinAt S (fun x ↦ (T x : E →ₗ[ℝ] F).detLineCongr (e₁ x).toLinearEquiv
      (e₂ x).toLinearEquiv (h x) (v x)) s x₀ := by
  have hS_eq (x : X) : S x = (e₂ x : F →L[ℝ] F') ∘L T x ∘L ((e₁ x).symm : E' →L[ℝ] E) := by
    ext u
    simpa using LinearMap.congr_fun (h x) ((e₁ x).symm u)
  have he₁' := he₁.continuousLinearEquiv_symm
  have he₂' := he₂.continuousLinearEquiv_symm
  have hS : ContinuousWithinAt S s x₀ := by
    simpa only [← hS_eq] using he₂.clm_comp (hT.clm_comp he₁')
  have hFS : IsFredholm (S x₀) :=
    (isFredholm_iff_of_comp_eq (e₁ x₀) (e₂ x₀) (by rw [hS_eq]; ext; simp)).1 hF
  -- A kernel chart `(S₀, q₀)` of `T x₀`, transported to a kernel chart `(Dₛ, qₛ)` of `S x₀`.
  -- Read on `T x`, this chart of `S x` has the moving data `(D₂ x, q x)`.
  obtain ⟨S₀, hS₀, G, hG, q₀, U, -, hxU, hinv⟩ := hF.exists_isOpen_kernelChart
  set Dₛ : S₀ →L[ℝ] F' := (e₂ x₀ : F →L[ℝ] F') ∘L S₀.subtypeL with hDₛ_def
  set qₛ : E' × S₀ →L[ℝ] G :=
    q₀ ∘L (((e₁ x₀).symm : E' →L[ℝ] E) ∘L fst ℝ E' S₀).prod (snd ℝ E' S₀) with hqₛ_def
  set D₂ : X → S₀ →L[ℝ] F := fun x ↦ ((e₂ x).symm : F' →L[ℝ] F) ∘L Dₛ with hD₂_def
  set q : X → E × S₀ →L[ℝ] G :=
    fun x ↦ qₛ ∘L ((e₁ x : E →L[ℝ] E') ∘L fst ℝ E S₀).prod (snd ℝ E S₀) with hq_def
  have hD₂ : ContinuousWithinAt D₂ s x₀ := he₂'.clm_comp continuousWithinAt_const
  have hq : ContinuousWithinAt q s x₀ := continuousWithinAt_const.clm_comp
    ((prodL ℝ).continuous.continuousAt.comp_continuousWithinAt
      (f := fun x ↦ ((e₁ x : E →L[ℝ] E') ∘L fst ℝ E S₀, snd ℝ E S₀))
      ((he₁.clm_comp continuousWithinAt_const).prodMk continuousWithinAt_const))
  have h₀ : (((T x₀).coprod (D₂ x₀)).prod (q x₀)).IsInvertible := by
    have hD₂₀ : D₂ x₀ = S₀.subtypeL := by ext; simp [hD₂_def, hDₛ_def]
    have hq₀ : q x₀ = q₀ := by ext <;> simp [hq_def, hqₛ_def]
    rw [hD₂₀, hq₀]
    exact hinv _ hxU
  refine isDetLineCoherentWithinAt_of_eventually_sameRay hS hFS
    ((LinearEquiv.map_ne_zero_iff _).2 hv.ne_zero) (isInvertible_prod_coprod_of_comp_eq (h x₀) h₀)
    ?_
  filter_upwards [hv.eventually_sameRay hT h₀, eventually_detLineChartEquiv_eq_smul hT hD₂ hq h₀]
    with x hev₁ hev₂
  obtain ⟨h₁, hsr⟩ := hev₁
  obtain ⟨hx, h', c, hc, hcx⟩ := hev₂
  refine ⟨isInvertible_prod_coprod_of_comp_eq (h x) hx, ?_⟩
  have key := hsr.pos_smul_left hc
  rw [← hcx] at key
  rwa [detLineChartEquiv_detLineCongr_of_comp_eq (h x) hx,
    detLineChartEquiv_detLineCongr_of_comp_eq (h x₀) h₀]

/-- **Naturality of continuous orientations.** Let `T` be a family of operators continuous on `s`
and Fredholm at every point of `s`. Transporting a family coherent for `T` on `s` along squares
`S x ∘ e₁ x = e₂ x ∘ T x` of families of isomorphisms continuous on `s` gives a family coherent
for `S` on `s`. -/
theorem IsDetLineCoherentOn.detLineCongr (hv : IsDetLineCoherentOn T v s) (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, IsFredholm (T x)) (he₁ : ContinuousOn (fun x ↦ (e₁ x : E →L[ℝ] E')) s)
    (he₂ : ContinuousOn (fun x ↦ (e₂ x : F →L[ℝ] F')) s)
    (h : ∀ x, (S x : E' →ₗ[ℝ] F') ∘ₗ (e₁ x).toLinearEquiv.toLinearMap =
      (e₂ x).toLinearEquiv.toLinearMap ∘ₗ (T x : E →ₗ[ℝ] F)) :
    IsDetLineCoherentOn S (fun x ↦ (T x : E →ₗ[ℝ] F).detLineCongr (e₁ x).toLinearEquiv
      (e₂ x).toLinearEquiv (h x) (v x)) s :=
  isDetLineCoherentOn_iff.2 fun x hx ↦ (isDetLineCoherentOn_iff.1 hv x hx).detLineCongr (hT x hx)
    (hF x hx) (he₁ x hx) (he₂ x hx) h

end Coherent

section Transport

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  {T : ℝ → E →L[ℝ] F} {S : ℝ → E' →L[ℝ] F'} {e₁ : ℝ → E ≃L[ℝ] E'} {e₂ : ℝ → F ≃L[ℝ] F'}
  {a b : ℝ}

/-- **Naturality of orientation transport.** Let `S t ∘ e₁ t = e₂ t ∘ T t` along paths of
isomorphisms `e₁` of the sources and `e₂` of the targets, continuous between `a` and `b`. Then
transporting an orientation along `S` from `a` to `b` is transporting it along `T`, conjugated by
the transports of determinant lines along the squares at `a` and at `b`. -/
theorem detLineOrientationTransport_map_detLineCongr (hT : ContinuousOn T (uIcc a b))
    (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) (hS : ContinuousOn S (uIcc a b))
    (hFS : ∀ t ∈ uIcc a b, IsFredholm (S t))
    (he₁ : ContinuousOn (fun t ↦ (e₁ t : E →L[ℝ] E')) (uIcc a b))
    (he₂ : ContinuousOn (fun t ↦ (e₂ t : F →L[ℝ] F')) (uIcc a b))
    (h : ∀ t, (S t : E' →ₗ[ℝ] F') ∘ₗ (e₁ t).toLinearEquiv.toLinearMap =
      (e₂ t).toLinearEquiv.toLinearMap ∘ₗ (T t : E →ₗ[ℝ] F))
    (o : Module.Ray ℝ (T a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hS hFS (Module.Ray.map ((T a : E →ₗ[ℝ] F).detLineCongr
        (e₁ a).toLinearEquiv (e₂ a).toLinearEquiv (h a)) o) =
      Module.Ray.map ((T b : E →ₗ[ℝ] F).detLineCongr (e₁ b).toLinearEquiv (e₂ b).toLinearEquiv
        (h b)) (detLineOrientationTransport a b hT hF o) := by
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hv₀
  rw [Module.Ray.map_apply, detLineOrientationTransport_rayOfNeZero hT hF hv,
    Module.Ray.map_apply]
  exact detLineOrientationTransport_rayOfNeZero hS hFS (hv.detLineCongr hT hF he₁ he₂ h)

/-- **Transport along a path of target isomorphisms.** For a Fredholm operator `T₀` and a path
`A` of isomorphisms of its target, transporting an orientation along `t ↦ A t ∘ T₀` from `a` to
`b` is the transport of determinant lines along `A b ∘ (A a)⁻¹`. -/
theorem detLineOrientationTransport_comp_left {T₀ : E →L[ℝ] F} (hT₀ : IsFredholm T₀)
    {A : ℝ → F ≃L[ℝ] F'} (hA : ContinuousOn (fun t ↦ (A t : F →L[ℝ] F')) (uIcc a b))
    (o : Module.Ray ℝ (T₀ : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun t ↦ (A t : F →L[ℝ] F') ∘L T₀) a b
        (hA.clm_comp continuousOn_const) (fun t _ ↦ hT₀.equiv_comp (A t))
        (Module.Ray.map ((T₀ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
          (A a).toLinearEquiv (LinearMap.ext fun _ ↦ rfl)) o) =
      Module.Ray.map ((T₀ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E) (A b).toLinearEquiv
        (LinearMap.ext fun _ ↦ rfl)) o := by
  -- Both sides are read off from `T₀` through the squares `(A t ∘ T₀) ∘ 1 = A t ∘ T₀`.
  have := detLineOrientationTransport_map_detLineCongr (T := fun _ ↦ T₀)
    (S := fun t ↦ (A t : F →L[ℝ] F') ∘L T₀) (e₁ := fun _ ↦ ContinuousLinearEquiv.refl ℝ E)
    (e₂ := A) continuousOn_const (fun _ _ ↦ hT₀) (hA.clm_comp continuousOn_const)
    (fun t _ ↦ hT₀.equiv_comp (A t)) continuousOn_const hA (fun _ ↦ LinearMap.ext fun _ ↦ rfl) o
  rwa [detLineOrientationTransport_const hT₀, id] at this

end Transport

end TauCeti
