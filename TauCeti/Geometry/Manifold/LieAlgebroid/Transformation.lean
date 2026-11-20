/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Basic
public import TauCeti.Geometry.Manifold.VectorField.InfinitesimalAction
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Transformation Lie algebroids

An infinitesimal action `ξ ↦ ξ_M` of a finite-dimensional real Lie algebra `𝔤` on a manifold `M`
(`TauCeti.InfinitesimalAction`, with `(⁅ξ, η⁆)_M = -[ξ_M, η_M]`) makes the trivial bundle
`M × 𝔤` a Lie algebroid, the **transformation** (or action) Lie algebroid
`TauCeti.LieAlgebroid.transformation`. Its anchor is the Lie algebra homomorphism `ξ ↦ -ξ_M`
evaluated pointwise, `ρ(u)(x) = -(u x)_M(x)`, and the bracket of two `𝔤`-valued functions is
`[u, v](x) = ⁅u x, v x⁆ + dv_x(ρ(u)(x)) - du_x(ρ(v)(x))`.
On constant functions the bracket is the bracket of `𝔤`
(`TauCeti.LieAlgebroid.transformation_bracket_of_forall_eq`), and the anchor at `x` vanishes
exactly on the isotropy algebra `𝔤_x` of the action
(`TauCeti.LieAlgebroid.transformation_anchor_eq_zero_iff`).

A Lie algebra carries no norm, while the fibre of a smooth vector bundle is modelled on a normed
space. The fibre is therefore a finite-dimensional normed space `F` identified with `𝔤` by a
linear isomorphism `e : F ≃ₗ[ℝ] 𝔤`; for a normed Lie algebra such as `GroupLieAlgebra I G`, `e`
is the identity.

The Leibniz rule follows from the two derivative terms. The Jacobi identity is not a pointwise
computation: the Jacobiator of three sections, and the failure of the anchor to intertwine the
brackets, are both linear over smooth functions, and they vanish on constant sections because
`ξ ↦ -ξ_M` is a Lie algebra homomorphism. Since the constant sections form a global frame of
the trivial bundle, both vanish identically.

## Main definitions

* `TauCeti.LieAlgebroid.transformation a e`: the transformation Lie algebroid of an infinitesimal
  action `a` of `𝔤`, on the trivial bundle with fibre `F ≃ₗ[ℝ] 𝔤`.

## Main results

* `TauCeti.LieAlgebroid.transformation_anchor_apply` and
  `TauCeti.LieAlgebroid.transformation_bracket_apply`: the anchor and bracket formulas.
* `TauCeti.LieAlgebroid.transformation_bracket_of_forall_eq`: the bracket of constant sections
  is the bracket of `𝔤`.
* `TauCeti.LieAlgebroid.transformation_anchor_bracket`: the anchor intertwines the bracket of
  sections with the Lie bracket of vector fields, with no Hausdorff or finite-dimensionality
  hypothesis on the base.
* `TauCeti.LieAlgebroid.transformation_anchor_eq_zero_iff`: the anchor at `x` vanishes exactly on
  the isotropy algebra of the action at `x`.
* `TauCeti.LieAlgebroid.transformation_zero_anchor_apply` and
  `TauCeti.LieAlgebroid.transformation_zero_bracket_apply`: for the trivial action the
  transformation algebroid is the bundle of Lie algebras `M × 𝔤`, with zero anchor and the
  pointwise bracket.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Chapter 3 (action Lie algebroids).
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), 1–107 (action Lie algebroids).
-/

public section

noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff

namespace TauCeti

namespace LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  (a : InfinitesimalAction 𝔤 I M) (e : F ≃ₗ[ℝ] 𝔤)

/-! ### The anchor and bracket on `F`-valued functions -/

/-- The anchor vector field `x ↦ -(e (u x))_M(x)` of an `F`-valued function `u`. -/
private def tAnchor (u : M → F) : Π x : M, TangentSpace I x :=
  fun x ↦ -a (e (u x)) x

/-- The transformation bracket `⁅u x, v x⁆ + dv_x(ρ(u)(x)) - du_x(ρ(v)(x))` of two `F`-valued
functions. -/
private def tBracket (u v : M → F) : M → F :=
  fun x ↦ e.symm ⁅e (u x), e (v x)⁆ + mvfderiv I v x (tAnchor a e u x) -
    mvfderiv I u x (tAnchor a e v x)

/-- The derivative `ρ(u) f` of a function `f` along the anchor vector field of `u`. -/
private def tDeriv (u : M → F) (f : M → ℝ) : M → ℝ :=
  fun x ↦ mvfderiv I f x (tAnchor a e u x)

/-- The failure `ρ([u, v]) - [ρ(u), ρ(v)]` of the anchor to intertwine the brackets. -/
private def tDefect (u v : M → F) : Π x : M, TangentSpace I x :=
  tAnchor a e (tBracket a e u v) - mlieBracket I (tAnchor a e u) (tAnchor a e v)

/-- The Jacobiator `[u, [v, w]] - [[u, v], w] - [v, [u, w]]`. -/
private def tJacobiator (u v w : M → F) : M → F :=
  tBracket a e u (tBracket a e v w) - tBracket a e (tBracket a e u v) w -
    tBracket a e v (tBracket a e u w)

section Algebra

variable {a e}

private theorem tAnchor_add (u v : M → F) :
    tAnchor a e (u + v) = tAnchor a e u + tAnchor a e v := by
  ext x
  simp [tAnchor, add_comm]

private theorem tAnchor_neg (u : M → F) : tAnchor a e (-u) = -tAnchor a e u := by
  ext x
  simp [tAnchor]

private theorem tAnchor_smul (f : M → ℝ) (u : M → F) :
    tAnchor a e (f • u) = f • tAnchor a e u := by
  ext x
  simp [tAnchor]

private theorem tAnchor_const (c : F) : tAnchor a e (fun _ ↦ c) = -a (e c) :=
  (rfl)

private theorem tBracket_swap (u v : M → F) : tBracket a e v u = -tBracket a e u v := by
  ext x
  simp only [tBracket, Pi.neg_apply, ← lie_skew (e (u x)), map_neg]
  abel

private theorem tBracket_self (u : M → F) : tBracket a e u u = 0 := by
  ext x
  simp only [tBracket, lie_self, map_zero, zero_add, sub_self, Pi.zero_apply]

private theorem tBracket_neg_left (u v : M → F) :
    tBracket a e (-u) v = -tBracket a e u v := by
  ext x
  simp only [tBracket, tAnchor_neg, Pi.neg_apply, map_neg, neg_lie, mvfderiv_neg,
    _root_.neg_apply]
  abel

private theorem tBracket_neg_right (u v : M → F) :
    tBracket a e u (-v) = -tBracket a e u v := by
  rw [tBracket_swap, tBracket_neg_left, tBracket_swap, neg_neg]

private theorem tBracket_add_right {u v v' : M → F} (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (hv' : ContMDiff I 𝓘(ℝ, F) ∞ v') :
    tBracket a e u (v + v') = tBracket a e u v + tBracket a e u v' := by
  ext x
  simp only [tBracket, tAnchor_add, Pi.add_apply, map_add, lie_add,
    mvfderiv_add (hv.mdifferentiableAt (by simp)) (hv'.mdifferentiableAt (by simp)),
    _root_.add_apply]
  abel

private theorem tBracket_add_left {u u' v : M → F} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u)
    (hu' : ContMDiff I 𝓘(ℝ, F) ∞ u') :
    tBracket a e (u + u') v = tBracket a e u v + tBracket a e u' v := by
  rw [tBracket_swap, tBracket_add_right hu hu', tBracket_swap u, tBracket_swap u', neg_add,
    neg_neg, neg_neg]

/-- The Leibniz rule `[u, f • v] = f • [u, v] + (ρ(u) f) • v`. -/
private theorem tBracket_smul_right {u v : M → F} {f : M → ℝ} (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    tBracket a e u (f • v) = f • tBracket a e u v + tDeriv a e u f • v := by
  ext x
  simp only [tBracket, tDeriv, tAnchor_smul, Pi.add_apply, Pi.smul_apply',
    map_smul, lie_smul, mvfderiv_smul (hf.mdifferentiableAt (by simp))
      (hv.mdifferentiableAt (by simp)), _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  module

private theorem tDeriv_const (u : M → F) (c : ℝ) : tDeriv a e u (fun _ ↦ c) = 0 := by
  ext x
  simp [tDeriv, mvfderiv_const]

private theorem tBracket_const_smul_right {u v : M → F} (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (c : ℝ) : tBracket a e u (c • v) = c • tBracket a e u v := by
  have h := tBracket_smul_right (a := a) (e := e) (u := u) hv (contMDiff_const (c := c))
  rw [tDeriv_const, zero_smul, add_zero] at h
  exact h

private theorem tBracket_const_smul_left {u v : M → F} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u)
    (c : ℝ) : tBracket a e (c • u) v = c • tBracket a e u v := by
  rw [tBracket_swap, tBracket_const_smul_right hu, tBracket_swap, smul_neg, neg_neg]

private theorem tBracket_const (c d : F) :
    tBracket a e (fun _ ↦ c) (fun _ ↦ d) = fun _ ↦ e.symm ⁅e c, e d⁆ := by
  ext x
  simp [tBracket, mvfderiv_const]

private theorem tDefect_swap (u v : M → F) : tDefect a e v u = -tDefect a e u v := by
  rw [tDefect, tDefect, tBracket_swap, tAnchor_neg, mlieBracket_swap (V := tAnchor a e v)]
  abel

private theorem tDefect_const (c d : F) : tDefect a e (fun _ ↦ c) (fun _ ↦ d) = 0 := by
  ext x
  simp only [tDefect, tBracket_const, tAnchor_const, LinearEquiv.apply_symm_apply,
    InfinitesimalAction.map_lie, Pi.sub_apply, neg_neg, mlieBracket_neg_left,
    mlieBracket_neg_right, sub_self, Pi.zero_apply]

private theorem tJacobiator_swap₁₂ (u v w : M → F) :
    tJacobiator a e v u w = -tJacobiator a e u v w := by
  rw [tJacobiator, tJacobiator, tBracket_swap v u, tBracket_neg_left]
  abel

private theorem tJacobiator_swap₂₃ (u v w : M → F) :
    tJacobiator a e u w v = -tJacobiator a e u v w := by
  rw [tJacobiator, tJacobiator, tBracket_swap v w, tBracket_neg_right,
    tBracket_swap v (tBracket a e u w), tBracket_swap (tBracket a e u v) w]
  abel

private theorem tJacobiator_const (c d k : F) :
    tJacobiator a e (fun _ ↦ c) (fun _ ↦ d) (fun _ ↦ k) = 0 := by
  ext x
  simp only [tJacobiator, tBracket_const, LinearEquiv.apply_symm_apply, Pi.sub_apply,
    Pi.zero_apply, ← map_sub, lie_lie, sub_sub_cancel, sub_self]

end Algebra

variable [FiniteDimensional ℝ F]

/-! ### Smoothness -/

/-- The anchor at `x` as a continuous linear map `F →L[ℝ] T_xM`. -/
private def tAnchorCLM (x : M) : F →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap (-((a.eval x).comp e.toLinearMap))

/-- The bracket of `𝔤`, transported to `F` by `e`, as a continuous bilinear map. -/
private def lieCLM : F →L[ℝ] F →L[ℝ] F :=
  LinearMap.toContinuousLinearMap <| LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    LinearMap.mk₂ ℝ (fun v w ↦ e.symm ⁅e v, e w⁆)
      (fun v v' w ↦ by simp [add_lie]) (fun c v w ↦ by simp [smul_lie])
      (fun v w w' ↦ by simp [lie_add]) (fun c v w ↦ by simp [lie_smul])

variable {a e}

private theorem tAnchorCLM_apply (x : M) (w : F) : tAnchorCLM a e x w = -a (e w) x := by
  simp [tAnchorCLM]

/-- The anchor is a smooth section of the bundle of linear maps from the trivial bundle to the
tangent bundle. -/
private theorem contMDiff_tAnchorCLM :
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞ (fun x ↦ TotalSpace.mk' (F →L[ℝ] E)
      (E := fun x : M ↦ Trivial M F x →L[ℝ] TangentSpace I x) x (tAnchorCLM a e x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, contMDiffAt_clm_apply.2 fun w ↦ ?_⟩
  -- Read in the trivial bundle and in a tangent chart, the anchor applied to the constant `w` is
  -- the coordinate expression of the smooth vector field `-(e w)_M`.
  have h := (contMDiffAt_section_iff x₀).1 ((a.contMDiff (e w)).neg_section x₀)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)] with x hx
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.symmL_trivialization, ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_apply,
    tAnchorCLM_apply, map_neg, Pi.neg_apply,
    Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hx]
  exact (((trivializationAt E (TangentSpace I : M → Type _) x₀).linear ℝ hx).map_neg _).symm

private theorem contMDiff_tAnchor {u : M → F} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u) :
    ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, tAnchor a e u x⟩ : TangentBundle I M)) := by
  have h := contMDiff_tAnchorCLM (a := a) (e := e).clm_bundle_apply
    (Bundle.Trivial.contMDiff_mk_iff.2 ⟨contMDiff_id, hu⟩)
  simp only [tAnchorCLM_apply] at h
  exact h

private theorem mdifferentiableAt_tAnchor {u : M → F} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u) {x : M} :
    MDifferentiableAt I I.tangent (fun x ↦ (⟨x, tAnchor a e u x⟩ : TangentBundle I M)) x :=
  (contMDiff_tAnchor hu).mdifferentiableAt (by simp)

private theorem contMDiff_mvfderiv_tAnchor {u : M → F} {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] {f : M → F'} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u)
    (hf : ContMDiff I 𝓘(ℝ, F') ∞ f) :
    ContMDiff I 𝓘(ℝ, F') ∞ fun x ↦ mvfderiv I f x (tAnchor a e u x) :=
  contMDiffOn_univ.1 <| hf.contMDiffOn.contMDiffOn_mvfderiv_apply isOpen_univ
    (contMDiff_tAnchor hu).contMDiffOn (by simp)

private theorem contMDiff_tDeriv {u : M → F} {f : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) : ContMDiff I 𝓘(ℝ) ∞ (tDeriv a e u f) :=
  contMDiff_mvfderiv_tAnchor hu hf

private theorem contMDiff_tBracket {u v : M → F} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u)
    (hv : ContMDiff I 𝓘(ℝ, F) ∞ v) : ContMDiff I 𝓘(ℝ, F) ∞ (tBracket a e u v) := by
  have hlie : ContMDiff I 𝓘(ℝ, F) ∞ fun x ↦ lieCLM e (u x) (v x) :=
    ((lieCLM e).contDiff.comp_contMDiff hu).clm_apply hv
  exact (hlie.add (contMDiff_mvfderiv_tAnchor hu hv)).sub (contMDiff_mvfderiv_tAnchor hv hu)

/-! ### The anchor intertwines the brackets -/

variable [CompleteSpace E]

private theorem tDefect_add_right {u v v' : M → F} (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (hv' : ContMDiff I 𝓘(ℝ, F) ∞ v') :
    tDefect a e u (v + v') = tDefect a e u v + tDefect a e u v' := by
  ext x
  simp only [tDefect, tBracket_add_right hv hv', tAnchor_add, Pi.sub_apply, Pi.add_apply,
    mlieBracket_add_right (mdifferentiableAt_tAnchor hv) (mdifferentiableAt_tAnchor hv')]
  abel

private theorem tDefect_smul_right {u v : M → F} {f : M → ℝ} (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) : tDefect a e u (f • v) = f • tDefect a e u v := by
  ext x
  simp only [tDefect, tBracket_smul_right hv hf, tAnchor_add, tAnchor_smul, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply',
    mlieBracket_smul_right (hf.mdifferentiableAt (by simp)) (mdifferentiableAt_tAnchor hv),
    tDeriv, smul_sub]
  abel

/-- The anchor intertwines the transformation bracket with the Lie bracket of vector fields. -/
private theorem tAnchor_tBracket {u v : M → F} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u)
    (hv : ContMDiff I 𝓘(ℝ, F) ∞ v) :
    tAnchor a e (tBracket a e u v) = mlieBracket I (tAnchor a e u) (tAnchor a e v) := by
  -- The defect is linear over smooth functions in its second argument, so it vanishes when the
  -- first argument is constant; by skew-symmetry it is then linear in its first argument too.
  have hc (c : F) {v : M → F} (hv : ContMDiff I 𝓘(ℝ, F) ∞ v) :
      tDefect a e (fun _ ↦ c) v = 0 :=
    Manifold.eq_zero_of_contMDiff_tensorial_of_const (tDefect a e fun _ ↦ c)
      (fun _ _ hv hv' ↦ tDefect_add_right hv hv') (fun _ _ hf hv ↦ tDefect_smul_right hv hf)
      (tDefect_const c) hv
  have h : tDefect a e u v = 0 := by
    refine Manifold.eq_zero_of_contMDiff_tensorial_of_const (fun u ↦ tDefect a e u v)
      (fun u u' hu hu' ↦ ?_) (fun f u hf hu ↦ ?_) (fun c ↦ hc c hv) hu
    · rw [tDefect_swap, tDefect_add_right hu hu', tDefect_swap u, tDefect_swap u', neg_add,
        neg_neg, neg_neg]
    · rw [tDefect_swap, tDefect_smul_right hu hf, tDefect_swap u, smul_neg, neg_neg]
  exact sub_eq_zero.1 h

/-- The derivative along the anchor of a bracket is the commutator of the derivatives:
`ρ([u, v]) f = ρ(u) (ρ(v) f) - ρ(v) (ρ(u) f)`. -/
private theorem tDeriv_tBracket {u v : M → F} {f : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, F) ∞ u) (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    tDeriv a e (tBracket a e u v) f =
      tDeriv a e u (tDeriv a e v f) - tDeriv a e v (tDeriv a e u f) := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  ext x
  simp only [tDeriv, tAnchor_tBracket hu hv, Pi.sub_apply]
  exact mvfderiv_mlieBracket (hf x) (by simp) (mdifferentiableAt_tAnchor hu)
    (mdifferentiableAt_tAnchor hv)

/-! ### The Jacobi identity -/

omit [CompleteSpace E] in
private theorem tJacobiator_add_right {u v w w' : M → F} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u)
    (hv : ContMDiff I 𝓘(ℝ, F) ∞ v) (hw : ContMDiff I 𝓘(ℝ, F) ∞ w)
    (hw' : ContMDiff I 𝓘(ℝ, F) ∞ w') :
    tJacobiator a e u v (w + w') = tJacobiator a e u v w + tJacobiator a e u v w' := by
  rw [tJacobiator, tJacobiator, tJacobiator, tBracket_add_right hw hw',
    tBracket_add_right hw hw', tBracket_add_right hw hw',
    tBracket_add_right (contMDiff_tBracket hv hw) (contMDiff_tBracket hv hw'),
    tBracket_add_right (contMDiff_tBracket hu hw) (contMDiff_tBracket hu hw')]
  abel

private theorem tJacobiator_smul_right {u v w : M → F} {f : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, F) ∞ u) (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (hw : ContMDiff I 𝓘(ℝ, F) ∞ w) (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    tJacobiator a e u v (f • w) = f • tJacobiator a e u v w := by
  have hvf := contMDiff_tDeriv (a := a) (e := e) hv hf
  have huf := contMDiff_tDeriv (a := a) (e := e) hu hf
  have hvw := contMDiff_tBracket (a := a) (e := e) hv hw
  have huw := contMDiff_tBracket (a := a) (e := e) hu hw
  -- Expanding by the Leibniz rule leaves `(ρ(u) ρ(v) f - ρ(v) ρ(u) f - ρ([u, v]) f) • w`, which
  -- vanishes because the anchor intertwines the brackets.
  rw [tJacobiator, tJacobiator, tBracket_smul_right hw hf, tBracket_smul_right hw hf,
    tBracket_smul_right hw hf,
    tBracket_add_right (hf.smul hvw) (hvf.smul hw), tBracket_smul_right hvw hf,
    tBracket_smul_right hw hvf,
    tBracket_add_right (hf.smul huw) (huf.smul hw), tBracket_smul_right huw hf,
    tBracket_smul_right hw huf, tDeriv_tBracket hu hv hf]
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply']
  module

/-- The Jacobi identity for the transformation bracket of smooth functions. -/
private theorem tJacobiator_eq_zero {u v w : M → F}
    (hu : ContMDiff I 𝓘(ℝ, F) ∞ u) (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (hw : ContMDiff I 𝓘(ℝ, F) ∞ w) : tJacobiator a e u v w = 0 := by
  -- The Jacobiator is linear over smooth functions in its last argument and skew-symmetric, so it
  -- is linear in each argument; it vanishes on constants by the Jacobi identity of `𝔤`.
  have h₃ {u v : M → F} (hu : ContMDiff I 𝓘(ℝ, F) ∞ u) (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
      (hconst : ∀ c, tJacobiator a e u v (fun _ ↦ c) = 0) {w : M → F}
      (hw : ContMDiff I 𝓘(ℝ, F) ∞ w) : tJacobiator a e u v w = 0 :=
    Manifold.eq_zero_of_contMDiff_tensorial_of_const (tJacobiator a e u v)
      (fun _ _ hw hw' ↦ tJacobiator_add_right hu hv hw hw')
      (fun _ _ hf hw ↦ tJacobiator_smul_right hu hv hw hf) hconst hw
  have hccw (c d : F) {w : M → F} (hw : ContMDiff I 𝓘(ℝ, F) ∞ w) :
      tJacobiator a e (fun _ ↦ c) (fun _ ↦ d) w = 0 :=
    h₃ contMDiff_const contMDiff_const (tJacobiator_const c d) hw
  have hcvw (c : F) {v w : M → F} (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
      (hw : ContMDiff I 𝓘(ℝ, F) ∞ w) : tJacobiator a e (fun _ ↦ c) v w = 0 := by
    rw [← neg_eq_zero, ← tJacobiator_swap₂₃]
    exact h₃ contMDiff_const hw (fun d ↦ by rw [tJacobiator_swap₂₃, hccw c d hw, neg_zero]) hv
  rw [← neg_eq_zero, ← tJacobiator_swap₁₂, ← neg_eq_zero, ← tJacobiator_swap₂₃]
  exact h₃ hv hw (fun c ↦ by
    rw [tJacobiator_swap₂₃, tJacobiator_swap₁₂, neg_neg, hcvw c hv hw]) hu

/-! ### The transformation Lie algebroid -/

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] [CompleteSpace E] in
private theorem coe_add_fun (u v : Cₛ^∞⟮I; F, Trivial M F⟯) :
    (fun x ↦ ((u + v) x : F)) = (fun x ↦ (u x : F)) + fun x ↦ (v x : F) :=
  funext fun x ↦ congr_fun (ContMDiffSection.coe_add u v) x

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] [CompleteSpace E] in
private theorem coe_const_smul_fun (c : ℝ) (u : Cₛ^∞⟮I; F, Trivial M F⟯) :
    (fun x ↦ ((c • u) x : F)) = c • fun x ↦ (u x : F) :=
  funext fun x ↦ congr_fun (ContMDiffSection.coe_smul c u) x

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] [CompleteSpace E] in
private theorem coe_smul_fun (f : C^∞⟮I, M; ℝ⟯) (u : Cₛ^∞⟮I; F, Trivial M F⟯) :
    (fun x ↦ ((f • u) x : F)) = (f : M → ℝ) • fun x ↦ (u x : F) :=
  funext fun x ↦ ContMDiffSection.smul_apply f u x

omit [CompleteSpace E] in
variable (a e) in
/-- The transformation bracket of two smooth sections of the trivial bundle. -/
private def tBracketSection (u v : Cₛ^∞⟮I; F, Trivial M F⟯) : Cₛ^∞⟮I; F, Trivial M F⟯ where
  toFun := tBracket a e (fun x ↦ (u x : F)) fun x ↦ (v x : F)
  contMDiff_toFun := Bundle.Trivial.contMDiff_mk_iff.2
    ⟨contMDiff_id, contMDiff_tBracket u.contMDiff_coe_trivial v.contMDiff_coe_trivial⟩

omit [CompleteSpace E] in
private theorem coe_tBracketSection (u v : Cₛ^∞⟮I; F, Trivial M F⟯) :
    (fun x ↦ (tBracketSection a e u v x : F)) =
      tBracket a e (fun x ↦ (u x : F)) fun x ↦ (v x : F) :=
  (rfl)

omit [CompleteSpace E] in
private theorem tBracketSection_apply (u v : Cₛ^∞⟮I; F, Trivial M F⟯) (x : M) :
    tBracketSection a e u v x = tBracket a e (fun x ↦ (u x : F)) (fun x ↦ (v x : F)) x :=
  (rfl)

omit [CompleteSpace E] in
private theorem tBracketSection_add_left (u u' v : Cₛ^∞⟮I; F, Trivial M F⟯) :
    tBracketSection a e (u + u') v = tBracketSection a e u v + tBracketSection a e u' v :=
  ContMDiffSection.ext fun x ↦ by
    simp only [tBracketSection_apply, ↓coe_add_fun, Pi.add_apply,
      tBracket_add_left u.contMDiff_coe_trivial u'.contMDiff_coe_trivial]

omit [CompleteSpace E] in
private theorem tBracketSection_add_right (u v v' : Cₛ^∞⟮I; F, Trivial M F⟯) :
    tBracketSection a e u (v + v') = tBracketSection a e u v + tBracketSection a e u v' :=
  ContMDiffSection.ext fun x ↦ by
    simp only [tBracketSection_apply, ↓coe_add_fun, Pi.add_apply,
      tBracket_add_right v.contMDiff_coe_trivial v'.contMDiff_coe_trivial]

omit [CompleteSpace E] in
private theorem tBracketSection_const_smul_left (c : ℝ) (u v : Cₛ^∞⟮I; F, Trivial M F⟯) :
    tBracketSection a e (c • u) v = c • tBracketSection a e u v :=
  ContMDiffSection.ext fun x ↦ by
    simp only [tBracketSection_apply, ↓coe_const_smul_fun, Pi.smul_apply,
      tBracket_const_smul_left u.contMDiff_coe_trivial]

omit [CompleteSpace E] in
private theorem tBracketSection_const_smul_right (c : ℝ) (u v : Cₛ^∞⟮I; F, Trivial M F⟯) :
    tBracketSection a e u (c • v) = c • tBracketSection a e u v :=
  ContMDiffSection.ext fun x ↦ by
    simp only [tBracketSection_apply, ↓coe_const_smul_fun, Pi.smul_apply,
      tBracket_const_smul_right v.contMDiff_coe_trivial]

variable (a e) in
/-- The **transformation Lie algebroid** of an infinitesimal action `ξ ↦ ξ_M` of a Lie algebra
`𝔤` on `M`: the trivial bundle `M × F`, with `F ≃ₗ[ℝ] 𝔤` by `e`, the anchor `w ↦ -(e w)_M(x)`
at `x`, and the bracket `[u, v](x) = e⁻¹⁅e (u x), e (v x)⁆ + dv_x(ρ(u)(x)) - du_x(ρ(v)(x))` of
smooth sections. The anchor `ξ ↦ -ξ_M` is a Lie algebra homomorphism, because `ξ ↦ ξ_M` is an
antihomomorphism. -/
def transformation : LieAlgebroid I F (Trivial M F) where
  anchor :=
    { toFun := tAnchorCLM a e
      contMDiff_toFun := contMDiff_tAnchorCLM }
  bracket := LinearMap.mk₂ ℝ (tBracketSection a e) tBracketSection_add_left
    tBracketSection_const_smul_left tBracketSection_add_right tBracketSection_const_smul_right
  bracket_self u := ContMDiffSection.ext fun x ↦ by
    rw [LinearMap.mk₂_apply, tBracketSection_apply, tBracket_self, ContMDiffSection.coe_zero,
      Pi.zero_apply]
  bracket_bracket u v w := ContMDiffSection.ext fun x ↦ by
    have h := congr($(tJacobiator_eq_zero (a := a) (e := e) u.contMDiff_coe_trivial
      v.contMDiff_coe_trivial w.contMDiff_coe_trivial) x)
    rw [tJacobiator, Pi.sub_apply, Pi.sub_apply, sub_sub, Pi.zero_apply, sub_eq_zero] at h
    simp only [LinearMap.mk₂_apply, ContMDiffSection.coe_add, Pi.add_apply, tBracketSection_apply,
      coe_tBracketSection]
    exact h
  bracket_smul_apply u v f x := by
    rw [LinearMap.mk₂_apply, LinearMap.mk₂_apply, tBracketSection_apply, tBracketSection_apply,
      coe_smul_fun, tBracket_smul_right v.contMDiff_coe_trivial f.contMDiff]
    simp [tDeriv, tAnchor, tAnchorCLM_apply]

/-- The anchor of the transformation algebroid at `x` sends `w` to `-(e w)_M(x)`. -/
@[simp]
theorem transformation_anchor_apply (x : M) (w : F) :
    (transformation a e).anchor x w = -a (e w) x :=
  tAnchorCLM_apply x w

/-- The bracket of the transformation algebroid:
`[u, v](x) = e⁻¹⁅e (u x), e (v x)⁆ + dv_x(ρ(u)(x)) - du_x(ρ(v)(x))`, where
`ρ(u)(x) = -(e (u x))_M(x)`. -/
@[simp]
theorem transformation_bracket_apply (u v : Cₛ^∞⟮I; F, Trivial M F⟯) (x : M) :
    (transformation a e).bracket u v x =
      e.symm ⁅e (u x), e (v x)⁆ + mvfderiv I (fun y ↦ (v y : F)) x (-a (e (u x)) x) -
        mvfderiv I (fun y ↦ (u y : F)) x (-a (e (v x)) x) :=
  (rfl)

/-- On constant sections the bracket of the transformation algebroid is the Lie bracket of `𝔤`,
transported to `F` by `e`. -/
theorem transformation_bracket_of_forall_eq {u v : Cₛ^∞⟮I; F, Trivial M F⟯} {c d : F}
    (hu : ∀ x, u x = c) (hv : ∀ x, v x = d) (x : M) :
    (transformation a e).bracket u v x = e.symm ⁅e c, e d⁆ := by
  have hu' : (fun x ↦ (u x : F)) = fun _ ↦ c := funext hu
  have hv' : (fun x ↦ (v x : F)) = fun _ ↦ d := funext hv
  simp only [transformation_bracket_apply, hu', hv', hu x, hv x, mvfderiv_const,
    _root_.zero_apply, add_zero, sub_zero]

/-- The anchor of the transformation algebroid maps the bracket of two sections to the Lie
bracket of their anchor vector fields. Unlike `TauCeti.LieAlgebroid.anchor_bracket`, this needs
no Hausdorff or finite-dimensionality hypothesis on the base. -/
theorem transformation_anchor_bracket (u v : Cₛ^∞⟮I; F, Trivial M F⟯) (x : M) :
    (transformation a e).anchor x ((transformation a e).bracket u v x) =
      mlieBracket I ((transformation a e).anchorField u) ((transformation a e).anchorField v)
        x := by
  have hρ (w : Cₛ^∞⟮I; F, Trivial M F⟯) :
      ⇑((transformation a e).anchorField w) = tAnchor a e fun x ↦ (w x : F) := by
    ext y
    simp [tAnchor]
  rw [hρ, hρ, ← tAnchor_tBracket u.contMDiff_coe_trivial v.contMDiff_coe_trivial,
    transformation_anchor_apply]
  -- The bracket of `transformation a e` is `tBracket` applied to the underlying functions.
  rfl

/-- The anchor of the transformation algebroid vanishes on `w` at `x` exactly when `e w` lies in
the isotropy algebra `𝔤_x` of the action: the isotropy of the transformation algebroid is the
stabiliser algebra of the action. -/
theorem transformation_anchor_eq_zero_iff (x : M) (w : F) :
    (transformation a e).anchor x w = 0 ↔ e w ∈ a.isotropy x := by
  rw [transformation_anchor_apply, neg_eq_zero, InfinitesimalAction.mem_isotropy_iff]

/-- For the trivial action the transformation algebroid has zero anchor. -/
theorem transformation_zero_anchor_apply (x : M) (w : F) :
    (transformation (0 : InfinitesimalAction 𝔤 I M) e).anchor x w = 0 := by
  simp

/-- For the trivial action the transformation algebroid is the bundle of Lie algebras `M × 𝔤`:
its bracket is the pointwise bracket of `𝔤`. -/
theorem transformation_zero_bracket_apply (u v : Cₛ^∞⟮I; F, Trivial M F⟯) (x : M) :
    (transformation (0 : InfinitesimalAction 𝔤 I M) e).bracket u v x =
      e.symm ⁅e (u x), e (v x)⁆ := by
  -- The vanishing terms are zeros of `F`; the equation is stated in the fibre `Trivial M F x`,
  -- so `add_zero` and `sub_zero` are given that type explicitly.
  simp only [transformation_bracket_apply, InfinitesimalAction.zero_apply, Pi.zero_apply,
    neg_zero, map_zero, add_zero (M := F), sub_zero (G := F)]

end LieAlgebroid

end TauCeti
