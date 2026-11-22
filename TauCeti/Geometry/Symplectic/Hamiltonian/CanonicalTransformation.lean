/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# Hamiltonian dynamics under symplectic maps (canonical transformations)

Let `φ : M → M'` be a symplectic map from a smooth two-form `σ` to a smooth two-form `σ'`
(`TauCeti.SmoothTwoForm.IsSymplecticMap`). At a point `x` where the differential `dφ_x` is
invertible, the flat map of `σ` is that of `σ'` conjugated by `dφ_x`, so the inverse flat maps
correspond too: `dφ_x ((σ♭_x)⁻¹ (ℓ ∘ dφ_x)) = (σ'♭_{φ x})⁻¹ ℓ` for every covector `ℓ`
(`TauCeti.SmoothTwoForm.IsSymplecticMap.mfderiv_inverse_flat_comp`). When one flat map is not
invertible neither is the other, and both inverses are zero, so this needs no nondegeneracy of
either form and holds on any model, Banach or not.

Consequently, with `X_h = (σ'♭)⁻¹ dh`, wherever `dφ_x` is invertible and `h` is differentiable
at `φ x`:
* `dφ_x (X_{h ∘ φ}(x)) = X_h(φ x)`
  (`TauCeti.SmoothTwoForm.IsSymplecticMap.mfderiv_hamiltonianVectorField_comp`);
* `{h ∘ φ, h' ∘ φ}(x) = {h, h'}(φ x)`
  (`TauCeti.SmoothTwoForm.IsSymplecticMap.poissonBracket_comp`);
* `φ` carries integral curves of `X_{h ∘ φ}` to integral curves of `X_h`
  (`TauCeti.SmoothTwoForm.IsSymplecticMap.isMIntegralCurve_comp_hamiltonianVectorField`).

For the equation `ι_X σ = dh` itself (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField`), which is
the meaningful notion for weakly nondegenerate forms, a differentiable symplectic map with
invertible differentials pulls a Hamiltonian vector field `V` of `h`, through
`VectorField.mpullback`, back to a Hamiltonian vector field of `h ∘ φ`
(`TauCeti.SmoothTwoForm.IsSymplecticMap.isHamiltonianVectorField_mpullback`).

For a symplectomorphism of nonzero order (`TauCeti.SmoothTwoForm.IsSymplectomorphism`) the
differentiability hypotheses drop: where `h` is not differentiable neither is `h ∘ φ`, and both
differentials vanish. So `X_{h ∘ φ} = φ^* X_h` and `{h ∘ φ, h' ∘ φ} = {h, h'} ∘ φ` for all
functions, and a vector field is a Hamiltonian vector field of `h` exactly when its pullback is one
of `h ∘ φ`.

The finite-dimensional statements of `TauCeti/Geometry/Symplectic/Hamiltonian/Manifold.lean`
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp` and its companions)
assume nondegenerate forms and a smooth map; the statements here are their versions on arbitrary
models, for arbitrary forms and maps with invertible differentials, such as symplectomorphisms and
inclusions of open submanifolds.

## Main declarations

* `TauCeti.SmoothTwoForm.IsSymplecticMap.mfderiv_hamiltonianVectorField_comp` and
  `TauCeti.SmoothTwoForm.IsSymplectomorphism.hamiltonianVectorField_comp`: naturality of
  Hamiltonian vector fields.
* `TauCeti.SmoothTwoForm.IsSymplecticMap.poissonBracket_comp` and
  `TauCeti.SmoothTwoForm.IsSymplectomorphism.poissonBracket_comp`: naturality of Poisson brackets.
* `TauCeti.SmoothTwoForm.IsSymplecticMap.isMIntegralCurve_comp_hamiltonianVectorField` and
  `TauCeti.SmoothTwoForm.IsSymplectomorphism.isMIntegralCurve_comp_hamiltonianVectorField`:
  transport of Hamiltonian integral curves.
* `TauCeti.SmoothTwoForm.IsSymplecticMap.isHamiltonianVectorField_mpullback` and
  `TauCeti.SmoothTwoForm.IsSymplectomorphism.isHamiltonianVectorField_mpullback_iff`: pullback of
  Hamiltonian vector fields.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.3 (canonical transformations).
* P. R. Chernoff, J. E. Marsden, *Properties of Infinite Dimensional Hamiltonian Systems*,
  Lecture Notes in Mathematics 425, Springer, 1974 (weak and strong nondegeneracy).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {σ : SmoothTwoForm I M} {σ' : SmoothTwoForm I' M'} {φ : M → M'}

/-! ### Symplectic maps with invertible differentials -/

namespace IsSymplecticMap

/-- **Inverse flat maps through a symplectic map.** At a point where the differential `dφ_x` of a
symplectic map is invertible, `dφ_x ((σ♭_x)⁻¹ (ℓ ∘ dφ_x)) = (σ'♭_{φ x})⁻¹ ℓ` for every covector
`ℓ` at `φ x`. No nondegeneracy is assumed: when the flat maps are not invertible, both inverses
are zero. -/
theorem mfderiv_inverse_flat_comp (h : σ.IsSymplecticMap σ' φ) {x : M}
    (hx : (mfderiv I I' φ x).IsInvertible) (ℓ : TangentSpace I' (φ x) →L[ℝ] ℝ) :
    mfderiv I I' φ x ((σ.flat x).inverse (ℓ.comp (mfderiv I I' φ x))) =
      (σ'.flat (φ x)).inverse ℓ := by
  obtain ⟨e, he⟩ := hx
  -- Precomposition with `e` identifies the dual of `T_{φ x} M'` with the dual of `T_x M`, and
  -- conjugates the flat map of `σ'` into that of `σ`.
  let A := e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hflat : σ.flat x =
      (A.symm : _ →L[ℝ] _).comp ((σ'.flat (φ x)).comp (e : _ →L[ℝ] _)) := by
    ext v w
    simp [A, h.flat_apply, ← he]
  have hA : A (ℓ.comp (e : _ →L[ℝ] _)) = ℓ := ContinuousLinearMap.ext fun u ↦ by simp [A]
  rw [hflat, ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv, ← he]
  simp [hA]

/-- **Hamiltonian vector fields through a symplectic map.** Let `φ` be a symplectic map,
differentiable at `x` with invertible differential there. For a function `h` differentiable at
`φ x`, the differential of `φ` carries the Hamiltonian vector field of `h ∘ φ` at `x` to the
Hamiltonian vector field of `h` at `φ x`. No nondegeneracy of the forms is assumed. -/
theorem mfderiv_hamiltonianVectorField_comp (h : σ.IsSymplecticMap σ' φ) {x : M}
    (hφ : MDifferentiableAt I I' φ x) (hx : (mfderiv I I' φ x).IsInvertible) {g : M' → ℝ}
    (hg : MDifferentiableAt I' 𝓘(ℝ) g (φ x)) :
    mfderiv I I' φ x (σ.hamiltonianVectorField (g ∘ φ) x) =
      σ'.hamiltonianVectorField g (φ x) := by
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, mvfderiv_comp x hg hφ]
  exact h.mfderiv_inverse_flat_comp hx _

/-- **Poisson brackets through a symplectic map.** Let `φ` be a symplectic map, differentiable at
`x` with invertible differential there. For functions `g` and `k` differentiable at `φ x`, the
Poisson bracket of `g ∘ φ` and `k ∘ φ` at `x` is the Poisson bracket of `g` and `k` at `φ x`. -/
theorem poissonBracket_comp (h : σ.IsSymplecticMap σ' φ) {x : M}
    (hφ : MDifferentiableAt I I' φ x) (hx : (mfderiv I I' φ x).IsInvertible) {g k : M' → ℝ}
    (hg : MDifferentiableAt I' 𝓘(ℝ) g (φ x)) (hk : MDifferentiableAt I' 𝓘(ℝ) k (φ x)) :
    σ.poissonBracket (g ∘ φ) (k ∘ φ) x = σ'.poissonBracket g k (φ x) := by
  rw [poissonBracket_def, poissonBracket_def, ← h.apply x,
    h.mfderiv_hamiltonianVectorField_comp hφ hx hg, h.mfderiv_hamiltonianVectorField_comp hφ hx hk]

/-- **Hamiltonian integral curves through a symplectic map.** Let `φ` be a symplectic map and `γ`
an integral curve of the Hamiltonian vector field of `g ∘ φ`. If along `γ` the map `φ` is
differentiable with invertible differentials and `g` is differentiable at the image points, then
`φ ∘ γ` is an integral curve of the Hamiltonian vector field of `g`. -/
theorem isMIntegralCurve_comp_hamiltonianVectorField (h : σ.IsSymplecticMap σ' φ) {g : M' → ℝ}
    {γ : ℝ → M} (hφ : ∀ t, MDifferentiableAt I I' φ (γ t))
    (hx : ∀ t, (mfderiv I I' φ (γ t)).IsInvertible)
    (hg : ∀ t, MDifferentiableAt I' 𝓘(ℝ) g (φ (γ t)))
    (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField (g ∘ φ))) :
    IsMIntegralCurve (φ ∘ γ) (σ'.hamiltonianVectorField g) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact hγ.map_of_mfderiv_eq (fun t _ ↦ hφ t)
    fun t _ ↦ h.mfderiv_hamiltonianVectorField_comp (hφ t) (hx t) (hg t)

/-- **Hamiltonian vector fields pull back along symplectic maps.** Let `φ` be a differentiable
symplectic map whose differentials are all invertible, and `V` a Hamiltonian vector field of `g`
for `σ'`, with `g` differentiable along `φ`. Then the pullback of `V` along `φ` is a Hamiltonian
vector field of `g ∘ φ` for `σ`. No nondegeneracy of the forms is assumed. -/
theorem isHamiltonianVectorField_mpullback (h : σ.IsSymplecticMap σ' φ)
    (hφ : MDifferentiable I I' φ) (hx : ∀ x, (mfderiv I I' φ x).IsInvertible) {g : M' → ℝ}
    {V : (y : M') → TangentSpace I' y} (hV : σ'.IsHamiltonianVectorField g V)
    (hg : ∀ x, MDifferentiableAt I' 𝓘(ℝ) g (φ x)) :
    σ.IsHamiltonianVectorField (g ∘ φ) (VectorField.mpullback I I' φ V) :=
  isHamiltonianVectorField_iff.2 fun x w ↦ by
    rw [← h.apply x, VectorField.mpullback_apply, (hx x).self_apply_inverse,
      isHamiltonianVectorField_iff.1 hV, mvfderiv_comp_apply x (hg x) (hφ x)]

end IsSymplecticMap

/-! ### Symplectomorphisms -/

namespace IsSymplectomorphism

variable {n : ℕ∞ω} {φ : M ≃ₘ^n⟮I, I'⟯ M'}

/-- **Hamiltonian vector fields through a symplectomorphism.** The differential of a
symplectomorphism of nonzero order carries the Hamiltonian vector field of `g ∘ φ` at `x` to the
Hamiltonian vector field of `g` at `φ x`, for every function `g`: where `g` is not differentiable,
neither is `g ∘ φ`, and both fields vanish. -/
theorem mfderiv_hamiltonianVectorField_comp (h : σ.IsSymplectomorphism σ' φ) (hn : n ≠ 0)
    (g : M' → ℝ) (x : M) :
    mfderiv I I' φ x (σ.hamiltonianVectorField (g ∘ φ) x) =
      σ'.hamiltonianVectorField g (φ x) := by
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, φ.mvfderiv_comp_diffeomorph hn]
  exact h.isSymplecticMap.mfderiv_inverse_flat_comp (φ.isInvertible_mfderiv hn (x := x)) _

/-- **The Hamiltonian vector field of a composite with a symplectomorphism** of nonzero order is
the pullback of the Hamiltonian vector field: `X_{g ∘ φ} = φ^* X_g`, for every function `g`. -/
theorem hamiltonianVectorField_comp (h : σ.IsSymplectomorphism σ' φ) (hn : n ≠ 0)
    (g : M' → ℝ) :
    σ.hamiltonianVectorField (g ∘ φ) =
      VectorField.mpullback I I' φ (σ'.hamiltonianVectorField g) :=
  funext fun x ↦ (φ.isInvertible_mfderiv hn (x := x)).injective <| by
    rw [h.mfderiv_hamiltonianVectorField_comp hn, φ.mfderiv_apply_mpullback hn]

/-- **Poisson brackets through a symplectomorphism.** For a symplectomorphism of nonzero order,
`{g ∘ φ, k ∘ φ} = {g, k} ∘ φ` for all functions `g` and `k`. -/
theorem poissonBracket_comp (h : σ.IsSymplectomorphism σ' φ) (hn : n ≠ 0) (g k : M' → ℝ)
    (x : M) : σ.poissonBracket (g ∘ φ) (k ∘ φ) x = σ'.poissonBracket g k (φ x) := by
  rw [poissonBracket_def, poissonBracket_def, ← h.isSymplecticMap.apply x,
    h.mfderiv_hamiltonianVectorField_comp hn, h.mfderiv_hamiltonianVectorField_comp hn]

/-- **Hamiltonian integral curves through a symplectomorphism.** A symplectomorphism of nonzero
order carries integral curves of the Hamiltonian vector field of `g ∘ φ` to integral curves of the
Hamiltonian vector field of `g`, for every function `g`. -/
theorem isMIntegralCurve_comp_hamiltonianVectorField (h : σ.IsSymplectomorphism σ' φ)
    (hn : n ≠ 0) {g : M' → ℝ} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField (g ∘ φ))) :
    IsMIntegralCurve (φ ∘ γ) (σ'.hamiltonianVectorField g) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact hγ.map_of_mfderiv_eq (fun t _ ↦ φ.mdifferentiable hn (γ t))
    fun t _ ↦ h.mfderiv_hamiltonianVectorField_comp hn g (γ t)

/-- **Hamiltonian vector fields through a symplectomorphism.** For a symplectomorphism `φ` of
nonzero order, the pullback along `φ` of a vector field `V` is a Hamiltonian vector field of
`g ∘ φ` exactly when `V` is a Hamiltonian vector field of `g`, for every function `g`. -/
theorem isHamiltonianVectorField_mpullback_iff (h : σ.IsSymplectomorphism σ' φ) (hn : n ≠ 0)
    {g : M' → ℝ} {V : (y : M') → TangentSpace I' y} :
    σ.IsHamiltonianVectorField (g ∘ φ) (VectorField.mpullback I I' φ V) ↔
      σ'.IsHamiltonianVectorField g V := by
  -- Both conditions say `σ'(V (φ x), dφ w) = dg (dφ w)`, and the differentials `dφ` are onto.
  have key : ∀ x (w : TangentSpace I x),
      σ.eval₂ x (VectorField.mpullback I I' φ V x) w =
        σ'.eval₂ (φ x) (V (φ x)) (mfderiv I I' φ x w) := fun x w ↦ by
    rw [← h.isSymplecticMap.apply x, φ.mfderiv_apply_mpullback hn]
  simp only [isHamiltonianVectorField_iff, key, φ.mvfderiv_comp_diffeomorph hn,
    ContinuousLinearMap.comp_apply]
  refine ⟨fun H y u ↦ ?_, fun H x w ↦ H (φ x) _⟩
  obtain ⟨x, rfl⟩ : ∃ x, φ x = y := ⟨φ.symm y, φ.apply_symm_apply y⟩
  obtain ⟨w, rfl⟩ := (φ.isInvertible_mfderiv hn (x := x)).surjective u
  exact H x w

end IsSymplectomorphism

end SmoothTwoForm

end TauCeti
