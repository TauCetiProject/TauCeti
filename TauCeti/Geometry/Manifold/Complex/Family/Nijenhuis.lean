/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Nijenhuis equations in a product trivialization

In a smooth product trivialization with constant base complex structure `i`, as in linear
holomorphic base coordinates, a complex-structure family has block form
`J(a,v) = (i a, α a + j v)`. Only `α` and `j` vary with the point. Its mixed, horizontal and
vertical Nijenhuis components are computed here on the native smooth almost-complex-structure
carrier. Total vanishing is equivalent to the mixed, horizontal and fibrewise equations.

The formulas `mixedTerm` and `horizontalTerm` follow Robbin–Salamon's corrected family
integrability calculation. Their vector-field bracket is the negative of Mathlib's bracket.
Consequently the native Nijenhuis values are `(0, -j M)` and `(0, -ζ)`, respectively.
All derivatives below are real derivatives on the total product, so the formulas include
both base and fibre variation.

## Main declarations

* `verticalTerm`, `fderiv_blockEndomorphism_apply`, `fderiv_fiber_connection`: the vertical family
  expression and block/fibre Fréchet derivatives.
* `blockNijenhuisExpr` and `blockNijenhuisExpr_horizontal_vertical`,
  `blockNijenhuisExpr_horizontal_horizontal`, `blockNijenhuisExpr_vertical_vertical`: raw
  normed-space Nijenhuis expression and component formulas (without finite-dimensionality).
* `nijenhuis_horizontal_vertical` and `nijenhuis_horizontal_horizontal`: the mixed and horizontal
  component formulas.
* `nijenhuis_vertical_vertical`: the fibrewise component formula.
* `lieBracket_fiber_eq`: the native fibre bracket and its sign comparison with the source bracket.
* `nijenhuis_eq_zero_iff`: the full vanishing criterion.

## References

* J. W. Robbin and D. A. Salamon, *Corrigendum to A construction of the Deligne–Mumford
  orbifold*, J. Eur. Math. Soc. 9 (2007), 901–905, Lemma A and the subsequent Remark.
-/

public noncomputable section

open scoped Manifold Topology

namespace TauCeti.ComplexStructureFamily

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The block endomorphism `J(a,v) = (i a, α a + j v)` on a product, with constant base block `i`;
only `α` and `j` vary with the point. -/
def blockEndomorphism (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p : B × V) : (B × V) →L[ℝ] B × V :=
  (i.comp (ContinuousLinearMap.fst ℝ B V)).prod
    ((α p).comp (ContinuousLinearMap.fst ℝ B V) +
      (j p).comp (ContinuousLinearMap.snd ℝ B V))

/-- Evaluation of the block endomorphism on a base and a fibre vector. -/
@[simp]
theorem blockEndomorphism_apply (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p w : B × V) :
    blockEndomorphism i α j p w = (i w.1, α p w.1 + j p w.2) := (rfl)

/-- Expressing `blockEndomorphism` via `inl` and `inr` exposes its regularity in `(α, j)`. -/
theorem blockEndomorphism_eq_inl_add_inr (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p : B × V) :
    blockEndomorphism i α j p =
      (ContinuousLinearMap.inl ℝ B V).comp (i.comp (ContinuousLinearMap.fst ℝ B V)) +
        (ContinuousLinearMap.inr ℝ B V).comp
          ((α p).comp (ContinuousLinearMap.fst ℝ B V) +
            (j p).comp (ContinuousLinearMap.snd ℝ B V)) := by
  ext w <;> simp [blockEndomorphism_apply]

/-- Differentiability of `blockEndomorphism i α j` at `p` from differentiability of `α` and `j`. -/
theorem differentiableAt_blockEndomorphism {p : B × V}
    (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V}
    (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) :
    DifferentiableAt ℝ (blockEndomorphism i α j) p := by
  rw [funext (blockEndomorphism_eq_inl_add_inr i α j)]
  exact (differentiableAt_const _).add ((differentiableAt_const _).clm_comp
    ((hα.clm_comp (differentiableAt_const _)).add (hj.clm_comp (differentiableAt_const _))))

/-- Fréchet derivative of `blockEndomorphism i α j`: the constant base block differentiates to `0`,
while the vertical block differentiates to `fderiv ℝ α q h w.1 + fderiv ℝ j q h w.2`. -/
theorem fderiv_blockEndomorphism_apply (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {q : B × V}
    (hα : DifferentiableAt ℝ α q) (hj : DifferentiableAt ℝ j q) (h w : B × V) :
    fderiv ℝ (blockEndomorphism i α j) q h w = (0, fderiv ℝ α q h w.1 + fderiv ℝ j q h w.2) := by
  have h1 := (differentiableAt_blockEndomorphism i hα hj).hasFDerivAt.clm_apply
    (hasFDerivAt_const w q)
  have hd := ((hasFDerivAt_const (i w.1) q).prodMk
    ((hα.hasFDerivAt.clm_apply (hasFDerivAt_const w.1 q)).add
      (hj.hasFDerivAt.clm_apply (hasFDerivAt_const w.2 q)))).congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq (funext fun r ↦ blockEndomorphism_apply i α j r w))
  simpa using congrArg (fun D : (B × V) →L[ℝ] B × V ↦ D h) (h1.unique hd)

/-- The corrected mixed equation `dj(a) + j dj(ia) + j L_(αa) j`, evaluated on `v`.
The Lie derivative here is `L_ξ j = dj(ξ) + j Dξ - Dξ j`. -/
def mixedTerm (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p : B × V) (a : B) (v : V) : V :=
  fderiv ℝ j p (a, 0) v + j p (fderiv ℝ j p (i a, 0) v) +
    j p (fderiv ℝ j p (0, α p a) v +
      j p (fderiv ℝ α p (0, v) a) - fderiv ℝ α p (0, j p v) a)

/-- Expansion of the mixed family equation in total-space derivatives. -/
theorem mixedTerm_def (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p : B × V) (a : B) (v : V) :
    mixedTerm i α j p a v =
      fderiv ℝ j p (a, 0) v + j p (fderiv ℝ j p (i a, 0) v) +
        j p (fderiv ℝ j p (0, α p a) v +
          j p (fderiv ℝ α p (0, v) a) - fderiv ℝ α p (0, j p v) a) := (rfl)

/-- The corrected horizontal curvature equation, evaluated on two constant base directions.
Its last two terms are the source bracket `[αa,αb] = D(αa)(αb) - D(αb)(αa)`,
which is the negative of Mathlib's vector-field bracket. -/
def horizontalTerm (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p : B × V) (a b : B) : V :=
  fderiv ℝ α p (i b, 0) a - j p (fderiv ℝ α p (b, 0) a) -
    fderiv ℝ α p (i a, 0) b + j p (fderiv ℝ α p (a, 0) b) +
    fderiv ℝ α p (0, α p b) a - fderiv ℝ α p (0, α p a) b

/-- Expansion of the horizontal family equation in total-space derivatives. -/
theorem horizontalTerm_def (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p : B × V) (a b : B) :
    horizontalTerm i α j p a b =
      fderiv ℝ α p (i b, 0) a - j p (fderiv ℝ α p (b, 0) a) -
        fderiv ℝ α p (i a, 0) b + j p (fderiv ℝ α p (a, 0) b) +
        fderiv ℝ α p (0, α p b) a - fderiv ℝ α p (0, α p a) b := (rfl)

/-- The vertical (fibrewise) Nijenhuis expression of `j` at `p`, evaluated on fibre vectors `v`
and `w`. Only fibre derivatives `(0, ·)` of `j` occur. -/
def verticalTerm (j : B × V → V →L[ℝ] V) (p : B × V) (v w : V) : V :=
  fderiv ℝ j p (0, j p v) w - fderiv ℝ j p (0, j p w) v +
    j p (fderiv ℝ j p (0, w) v) - j p (fderiv ℝ j p (0, v) w)

/-- Expansion of the vertical family equation in total-space derivatives. -/
theorem verticalTerm_def (j : B × V → V →L[ℝ] V) (p : B × V) (v w : V) :
    verticalTerm j p v w =
      fderiv ℝ j p (0, j p v) w - fderiv ℝ j p (0, j p w) v +
        j p (fderiv ℝ j p (0, w) v) - j p (fderiv ℝ j p (0, v) w) := (rfl)

/-- Directional derivative along the fibre `{p.1} × V` of `y ↦ α (p.1, y) a`. -/
theorem fderiv_fiber_connection {α : B × V → B →L[ℝ] V} {p : B × V}
    (hα : DifferentiableAt ℝ α p) (a : B) (v : V) :
    fderiv ℝ (fun y ↦ α (p.1, y) a) p.2 v = fderiv ℝ α p (0, v) a := by
  have hd : DifferentiableAt ℝ (fun q : B × V ↦ α q a) (p.1, p.2) := by
    rw [Prod.mk.eta]; exact hα.clm_apply (differentiableAt_const a)
  rw [fderiv_slice_right hd, Prod.mk.eta, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, fderiv_clm_apply hα (differentiableAt_const a)]
  simp

/-- The native bracket of two fibre vector fields from `α`, in total-space derivatives.
The source bracket in `horizontalTerm` is its negative. -/
theorem lieBracket_fiber_eq (α : B × V → B →L[ℝ] V) {p : B × V}
    (hα : DifferentiableAt ℝ α p) (a b : B) :
    VectorField.lieBracket ℝ (fun v ↦ α (p.1, v) a) (fun v ↦ α (p.1, v) b) p.2 =
      fderiv ℝ α p (0, α p a) b - fderiv ℝ α p (0, α p b) a := by
  simp only [VectorField.lieBracket_eq, fderiv_fiber_connection hα]

/-- Pointwise Nijenhuis expression of `blockEndomorphism i α j` at `p` on `u, w` (valid on arbitrary
real normed spaces without finite-dimensionality). -/
def blockNijenhuisExpr (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (p u w : B × V) : B × V :=
  let A := blockEndomorphism i α j
  fderiv ℝ A p (A p u) w - fderiv ℝ A p (A p w) u + A p (fderiv ℝ A p w u) - A p (fderiv ℝ A p u w)

/-- Expansion of `blockNijenhuisExpr` in terms of `fderiv ℝ (blockEndomorphism i α j)`. -/
theorem blockNijenhuisExpr_def (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (p u w : B × V) : blockNijenhuisExpr i α j p u w =
      fderiv ℝ (blockEndomorphism i α j) p (blockEndomorphism i α j p u) w -
        fderiv ℝ (blockEndomorphism i α j) p (blockEndomorphism i α j p w) u +
        blockEndomorphism i α j p (fderiv ℝ (blockEndomorphism i α j) p w u) -
        blockEndomorphism i α j p (fderiv ℝ (blockEndomorphism i α j) p u w) := (rfl)

/-- Raw mixed component of `blockNijenhuisExpr`: when `j(p)² = -1`, its value on `(a, 0)` and
`(0, v)` is `(0, -j p (mixedTerm i α j p a v))`. -/
theorem blockNijenhuisExpr_horizontal_vertical (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p)
    (hj_sq : ∀ v, j p (j p v) = -v) (a : B) (v : V) :
    blockNijenhuisExpr i α j p (a, 0) (0, v) = (0, -j p (mixedTerm i α j p a v)) := by
  -- Split `(i a, α p a)` into horizontal and vertical directions before differentiating.
  have hsplit : (i a, α p a) = (i a, 0) + (0, α p a) := by simp
  simp only [blockNijenhuisExpr_def, blockEndomorphism_apply, map_zero, add_zero, zero_add]
  rw [hsplit, map_add]
  simp only [add_apply, fderiv_blockEndomorphism_apply i hα hj, map_zero, add_zero, zero_add,
    Prod.mk_add_mk, Prod.mk_sub_mk, sub_zero, mixedTerm_def, map_add, map_sub, map_neg, hj_sq]
  congr 1
  abel

/-- Raw horizontal component of `blockNijenhuisExpr`: its value on `(a, 0)` and `(b, 0)` is
`(0, -horizontalTerm i α j p a b)`. -/
theorem blockNijenhuisExpr_horizontal_horizontal (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    (j : B × V → V →L[ℝ] V) {p : B × V}
    (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) (a b : B) :
    blockNijenhuisExpr i α j p (a, 0) (b, 0) = (0, -horizontalTerm i α j p a b) := by
  have hsplit (c : B) : (i c, α p c) = (i c, 0) + (0, α p c) := by simp
  simp only [blockNijenhuisExpr_def, blockEndomorphism_apply, map_zero, add_zero]
  rw [hsplit a, hsplit b, map_add, map_add]
  simp only [add_apply, fderiv_blockEndomorphism_apply i hα hj, map_zero, add_zero, zero_add,
    Prod.mk_add_mk, Prod.mk_sub_mk, sub_zero, horizontalTerm_def]
  congr 1
  abel

/-- Raw vertical component of `blockNijenhuisExpr`: its value on `(0, v)` and `(0, w)` is
`(0, verticalTerm j p v w)`, independent of `i` and `α`. -/
theorem blockNijenhuisExpr_vertical_vertical (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) (v w : V) :
    blockNijenhuisExpr i α j p (0, v) (0, w) = (0, verticalTerm j p v w) := by
  simp only [blockNijenhuisExpr_def, blockEndomorphism_apply, map_zero, zero_add,
    fderiv_blockEndomorphism_apply i hα hj, Prod.mk_add_mk, Prod.mk_sub_mk, sub_zero,
    verticalTerm_def]

/-! ### Native Nijenhuis tensor on finite-dimensional products -/

variable [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
  (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
  (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
  {p : B × V}
  (hJ : (fun q ↦ (J.toEndomorphism q : (B × V) →L[ℝ] B × V)) =ᶠ[𝓝 p]
    blockEndomorphism i α j)
  (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p)

include hJ

omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ V] in
private theorem j_apply_apply (v : V) : j p (j p v) = -v := by
  have h := SmoothAlmostComplexStructure.apply_apply J p (0, v)
  have hp := hJ.self_of_nhds
  simp only [hp] at h
  -- Read the square identity in the fixed model-space instances before taking its second part.
  change blockEndomorphism i α j p (blockEndomorphism i α j p (0, v)) = -(0, v) at h
  simpa using congrArg Prod.snd h

include hα hj

/-- When `J` agrees with `blockEndomorphism i α j` near `p` and `α`, `j` are differentiable at `p`,
the native Nijenhuis tensor `J.nijenhuis p` agrees with `blockNijenhuisExpr i α j p`. -/
theorem nijenhuis_eq_blockNijenhuisExpr (u w : B × V) :
    J.nijenhuis p u w = blockNijenhuisExpr i α j p u w := by
  have hA := differentiableAt_blockEndomorphism i hα hj
  have hd (z h : B × V) :
      fderiv ℝ (fun q ↦ blockEndomorphism i α j q z) p h =
        fderiv ℝ (blockEndomorphism i α j) p h z := by
    rw [fderiv_clm_apply hA (differentiableAt_const z)]
    simp
  rw [J.nijenhuis_eq_fderiv (blockEndomorphism i α j) p hJ, hd, hd, hd, hd, blockNijenhuisExpr_def]

/-- The mixed Nijenhuis component in a product trivialization. With the native Lie bracket
its sign is the negative of Robbin–Salamon's `j M`. -/
theorem nijenhuis_horizontal_vertical (a : B) (v : V) :
    J.nijenhuis p (a, 0) (0, v) = (0, -j p (mixedTerm i α j p a v)) :=
  (nijenhuis_eq_blockNijenhuisExpr J i α j hJ hα hj (a, 0) (0, v)).trans
    (blockNijenhuisExpr_horizontal_vertical i hα hj (j_apply_apply J i α j hJ) a v)

/-- The horizontal Nijenhuis component is the negative of the corrected horizontal equation.
This term is present even when the mixed equation vanishes. -/
theorem nijenhuis_horizontal_horizontal (a b : B) :
    J.nijenhuis p (a, 0) (b, 0) = (0, -horizontalTerm i α j p a b) :=
  (nijenhuis_eq_blockNijenhuisExpr J i α j hJ hα hj (a, 0) (b, 0)).trans
    (blockNijenhuisExpr_horizontal_horizontal i j hα hj a b)

/-- The vertical component is the ordinary fibre Nijenhuis expression: only fibre derivatives
of `j` occur, and the connection term `α` drops out. -/
theorem nijenhuis_vertical_vertical (v w : V) :
    J.nijenhuis p (0, v) (0, w) = (0, verticalTerm j p v w) :=
  (nijenhuis_eq_blockNijenhuisExpr J i α j hJ hα hj (0, v) (0, w)).trans
    (blockNijenhuisExpr_vertical_vertical i hα hj v w)

omit hJ hα hj in
private theorem snd_eq_zero_of_nijenhuis_eq_zero {u w : B × V} {x : V}
    (hN : J.nijenhuis p = 0) (h : J.nijenhuis p u w = (0, x)) : x = 0 := by
  have hz := (J.nijenhuis_model_eq_zero_iff p).mp hN u w
  simpa using congrArg Prod.snd (h.symm.trans hz)

/-- Vanishing of the native Nijenhuis tensor forces the corrected mixed equation. -/
theorem mixedTerm_eq_zero_of_nijenhuis_eq_zero
    (hN : J.nijenhuis p = 0) (a : B) (v : V) : mixedTerm i α j p a v = 0 := by
  have h := nijenhuis_horizontal_vertical J i α j hJ hα hj a v
  have hz : j p (mixedTerm i α j p a v) = 0 := by
    simpa using snd_eq_zero_of_nijenhuis_eq_zero J hN h
  have := congrArg (j p) hz
  simpa only [j_apply_apply J i α j hJ, map_zero, neg_eq_zero] using this

/-- Vanishing of the native Nijenhuis tensor also forces the horizontal curvature equation. -/
theorem horizontalTerm_eq_zero_of_nijenhuis_eq_zero
    (hN : J.nijenhuis p = 0) (a b : B) : horizontalTerm i α j p a b = 0 := by
  have h := nijenhuis_horizontal_horizontal J i α j hJ hα hj a b
  simpa using snd_eq_zero_of_nijenhuis_eq_zero J hN h

/-- The full product criterion: the mixed and horizontal equations, together with fibrewise
vanishing, are equivalent to vanishing of the total Nijenhuis tensor. In particular, when the
fibres are integrable, both of the corrected family equations remain necessary. -/
theorem nijenhuis_eq_zero_iff :
    J.nijenhuis p = 0 ↔
      (∀ a v, mixedTerm i α j p a v = 0) ∧
      (∀ a b, horizontalTerm i α j p a b = 0) ∧
      (∀ v w : V, J.nijenhuis p (0, v) (0, w) = 0) := by
  constructor
  · intro hN
    refine ⟨mixedTerm_eq_zero_of_nijenhuis_eq_zero J i α j hJ hα hj hN,
      horizontalTerm_eq_zero_of_nijenhuis_eq_zero J i α j hJ hα hj hN, ?_⟩
    exact fun v w ↦ (J.nijenhuis_model_eq_zero_iff p).mp hN (0, v) (0, w)
  · rintro ⟨hM, hH, hV⟩
    -- Use model-space bilinearity; the final tensor equality is handled by the shared bridge.
    let N : (B × V) →L[ℝ] (B × V) →L[ℝ] B × V := J.nijenhuis p
    have hmix (a : B) (v : V) : N (a, 0) (0, v) = 0 := by
      calc
        N (a, 0) (0, v) = (0, -j p (mixedTerm i α j p a v)) :=
          nijenhuis_horizontal_vertical J i α j hJ hα hj a v
        _ = 0 := by simp [hM]
    have hhor (a b : B) : N (a, 0) (b, 0) = 0 := by
      calc
        N (a, 0) (b, 0) = (0, -horizontalTerm i α j p a b) :=
          nijenhuis_horizontal_horizontal J i α j hJ hα hj a b
        _ = 0 := by simp [hH]
    have hrev (v : V) (a : B) : N (0, v) (a, 0) = 0 := by
      calc
        N (0, v) (a, 0) = -N (a, 0) (0, v) := J.nijenhuis_antisymm _ _
        _ = 0 := by rw [hmix, neg_zero]
    have htotal (u w : B × V) : N u w = 0 := by
      have hsplit (z : B × V) : z = (z.1, 0) + (0, z.2) := by simp
      rw [hsplit u, hsplit w]
      simp only [map_add, add_apply, hhor, hmix, hrev, zero_add]
      exact hV u.2 w.2
    exact (J.nijenhuis_model_eq_zero_iff p).mpr htotal

end TauCeti.ComplexStructureFamily
