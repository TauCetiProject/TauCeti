/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Identity
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.IsManifold.Pi
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Immersion.Diffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.Pi
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Iterated fibre products of submersions

For a `C^n` submersion `π : Y → M` (`1 ≤ n`) between finite-dimensional boundaryless real
manifolds, the `k`-fold fibre product `Y^[k]` (`k = m + 1 ≥ 1`) is the subtype
`TauCeti.IteratedFiberProduct π k = {y : Fin k → Y // ∀ i j, π (y i) = π (y j)}` equipped with
its subspace topology in `Fin k → Y`.

`TauCeti.iteratedFiberProductChartedSpace` constructs a `C^n` manifold structure on
`IteratedFiberProduct π (m + 1)` of dimension `(m + 1) * dim Y - m * dim M` by iterating the
binary transverse fibre-product atlas `TauCeti.transverseFiberProductChartedSpace`: the base case
`k = 1` pulls back the identity base change `{p : M × Y // id p.1 = π p.2}`, and the step from
`k` to `k + 1` forms the transverse fibre product of `IteratedFiberProduct.baseProj` with `π`.
Because `π` is a submersion, transversality holds unconditionally at every step, even when `Y` or
`M` is empty, and no separation or countability assumption is required for the manifold,
embedding, normal-form, or submersion assertions.

With this atlas:
* the subtype inclusion into `Fin (m + 1) → Y` is a `C^n` smooth embedding whose tangent image
  consists of tuples of tangent vectors with equal images under `mfderiv IY IM π`
  (`TauCeti.isSmoothEmbedding_coe_iteratedFiberProduct`,
  `TauCeti.mem_range_mfderiv_coe_iteratedFiberProduct_iff`);
* when `M` is Hausdorff, the multidiagonal `{z : Fin k → M | ∀ i j, z i = z j}` is closed and
  `IteratedFiberProduct π k` is a closed embedded submanifold of `Fin k → Y`, as the preimage of
  that multidiagonal under `Pi.map fun _ ↦ π`
  (`TauCeti.isClosedEmbedding_coe_iteratedFiberProduct`);
* around every point of `IteratedFiberProduct π (m + 1)` there is a product of maximal-atlas
  submersion charts of `Y` over the preferred target chart of `M` in which the submanifold is cut
  out by equality of the base-projection coordinates
  (`TauCeti.exists_submersionCharts_iteratedFiberProduct`);
* the smooth structure is independent of the order of iteration: splitting `k₁ + k₂` factors
  (`k₁ = m₁ + 1`, `k₂ = m₂ + 1`) gives a canonical `C^n` diffeomorphism with the transverse fibre
  product of `Y^[k₁]` and `Y^[k₂]` over `M`
  (`TauCeti.iteratedFiberProductSplitDiffeomorph`), covering both left and right iteration;
* the common projection `IteratedFiberProduct.baseProj` to `M` is a `C^n` submersion (surjective
  if and only if `π` is surjective), and every factor projection `IteratedFiberProduct.eval i` to
  `Y` is a surjective `C^n` submersion (`TauCeti.isSubmersion_baseProj`,
  `TauCeti.isSubmersion_eval`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (rank theorem for submersions), Theorem 4.26 (local sections of submersions),
  and Theorem 6.30 (transverse preimages).
-/

public section

open Function Set Module Topology
open scoped Manifold ContDiff

namespace TauCeti

section Set

variable {Y M : Type*} {π : Y → M}

/-- The `k`-fold fibre product `Y^[k]` of a map `π : Y → M` over `M`: the subtype of tuples
`y : Fin k → Y` whose coordinates share a common image under `π`. It is an abbreviation so that it
inherits the subspace topology and `Subtype.val` coercion from `Fin k → Y` directly. -/
abbrev IteratedFiberProduct (π : Y → M) (k : ℕ) : Type _ :=
  {y : Fin k → Y // ∀ i j, π (y i) = π (y j)}

/-- The underlying set of `IteratedFiberProduct π k` in `Fin k → Y` is the set of tuples whose
entries have equal images under `π`. -/
theorem range_coe_iteratedFiberProduct (π : Y → M) (k : ℕ) :
    range (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) =
      {y : Fin k → Y | ∀ i j, π (y i) = π (y j)} :=
  Subtype.range_coe_subtype

/-- A tuple in `Fin k → Y` belongs to the image of `IteratedFiberProduct π k` if and only if all
its coordinates have the same image under `π`. -/
theorem mem_range_coe_iteratedFiberProduct_iff {k : ℕ} {y : Fin k → Y} :
    y ∈ range (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) ↔
      ∀ i j, π (y i) = π (y j) := by
  rw [range_coe_iteratedFiberProduct]
  rfl

namespace IteratedFiberProduct

/-- The zero-fold fibre product consists of the unique empty tuple. -/
instance instUniqueZero : Unique (IteratedFiberProduct π 0) where
  default := ⟨Fin.elim0, fun i ↦ i.elim0⟩
  uniq _ := Subtype.ext (funext fun i ↦ i.elim0)

/-- The `i`-th factor projection `Y^[k] → Y`. -/
def eval {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) : Y :=
  y.1 i

/-- Evaluation at `i` reads the `i`-th coordinate of the underlying tuple. -/
@[simp]
theorem eval_apply {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) :
    eval i y = y.1 i := (rfl)

/-- Two points of `IteratedFiberProduct π k` are equal when all their factor projections agree. -/
theorem ext {k : ℕ} {y₁ y₂ : IteratedFiberProduct π k} (h : ∀ i, eval i y₁ = eval i y₂) :
    y₁ = y₂ :=
  Subtype.ext (funext h)

/-- Any two factor projections of `y : IteratedFiberProduct π k` have equal images under `π`. -/
theorem map_eval_eq {k : ℕ} (y : IteratedFiberProduct π k) (i j : Fin k) :
    π (eval i y) = π (eval j y) :=
  y.2 i j

/-- The diagonal inclusion `Y → Y^[k]` sending `z` to the constant tuple `(z, …, z)`. -/
def const (k : ℕ) (z : Y) : IteratedFiberProduct π k :=
  ⟨fun _ ↦ z, fun _ _ ↦ rfl⟩

/-- The underlying tuple of `const k z` is the constant function `Function.const (Fin k) z`. -/
@[simp]
theorem coe_const (k : ℕ) (z : Y) :
    (const (π := π) k z : Fin k → Y) = Function.const (Fin k) z := (rfl)

/-- Evaluating the diagonal tuple `const k z` at any index returns `z`. -/
theorem eval_const {k : ℕ} (i : Fin k) (z : Y) :
    eval i (const (π := π) k z) = z := (rfl)

/-- Every factor projection `eval i : Y^[k] → Y` is surjective, split by the diagonal `const k`. -/
theorem surjective_eval {k : ℕ} (i : Fin k) :
    Surjective (eval i : IteratedFiberProduct π k → Y) :=
  fun z ↦ ⟨const k z, rfl⟩

/-- The common projection `Y^[m + 1] → M` to the base, defined via the `0`-th factor and equal to
`π ∘ eval i` for every `i : Fin (m + 1)`. -/
def baseProj {m : ℕ} (y : IteratedFiberProduct π (m + 1)) : M :=
  π (y.1 0)

/-- The base projection agrees with `π (y.1 i)` at every coordinate `i : Fin (m + 1)`. -/
theorem baseProj_eq_apply {m : ℕ} (y : IteratedFiberProduct π (m + 1)) (i : Fin (m + 1)) :
    baseProj y = π (y.1 i) :=
  y.2 0 i

/-- Composing `π` with any factor projection `eval i` yields `baseProj`. -/
theorem map_eval_eq_baseProj {m : ℕ} (y : IteratedFiberProduct π (m + 1)) (i : Fin (m + 1)) :
    π (eval i y) = baseProj y :=
  (y.2 0 i).symm

/-- On a diagonal tuple `const (m + 1) z`, the base projection is `π z`. -/
@[simp]
theorem baseProj_const (m : ℕ) (z : Y) :
    baseProj (const (π := π) (m + 1) z) = π z := (rfl)

/-- The base projection `Y^[m + 1] → M` is surjective if and only if `π` is surjective. -/
theorem surjective_baseProj_iff {m : ℕ} :
    Surjective (baseProj : IteratedFiberProduct π (m + 1) → M) ↔ Surjective π :=
  ⟨fun h b ↦ by obtain ⟨y, rfl⟩ := h b; exact ⟨y.1 0, rfl⟩,
    fun h b ↦ by obtain ⟨z, rfl⟩ := h b; exact ⟨const (m + 1) z, rfl⟩⟩

end IteratedFiberProduct

end Set

section Topology

variable {Y M : Type*} [TopologicalSpace Y] {π : Y → M}

namespace IteratedFiberProduct

/-- Every factor projection `eval i : Y^[k] → Y` is continuous. -/
theorem continuous_eval {k : ℕ} (i : Fin k) :
    Continuous (eval i : IteratedFiberProduct π k → Y) :=
  (continuous_apply i).comp continuous_subtype_val

/-- The diagonal map `const k : Y → Y^[k]` is continuous. -/
theorem continuous_const (k : ℕ) :
    Continuous (const (π := π) k) :=
  (continuous_pi fun _ ↦ continuous_id).subtype_mk _

/-- When `π` is continuous, the base projection `baseProj : Y^[m + 1] → M` is continuous. -/
theorem continuous_baseProj [TopologicalSpace M] (hπ : Continuous π) (m : ℕ) :
    Continuous (baseProj : IteratedFiberProduct π (m + 1) → M) :=
  hπ.comp (continuous_eval 0)

end IteratedFiberProduct

/-- When the base `M` is Hausdorff and `π` is continuous, the equal-fibre locus in `Fin k → Y` is
closed as the preimage of the closed multidiagonal of `Fin k → M` under `Pi.map fun _ ↦ π`. -/
theorem isClosed_setOf_map_eq [TopologicalSpace M] [T2Space M] (hπ : Continuous π) (k : ℕ) :
    IsClosed {y : Fin k → Y | ∀ i j, π (y i) = π (y j)} := by
  have hdiag : IsClosed {z : Fin k → M | ∀ i j, z i = z j} := by
    have hEq : {z : Fin k → M | ∀ i j, z i = z j} =
        ⋂ (i : Fin k) (j : Fin k), {z | z i = z j} := by
      ext z
      simp
    rw [hEq]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_eq (continuous_apply i) (continuous_apply j)
  exact hdiag.preimage (continuous_pi fun i ↦ hπ.comp (continuous_apply i))

/-- When `M` is Hausdorff and `π` is continuous, the image of `IteratedFiberProduct π k` in
`Fin k → Y` is closed. -/
theorem isClosed_range_coe_iteratedFiberProduct [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosed (range (Subtype.val : IteratedFiberProduct π k → (Fin k → Y))) := by
  rw [range_coe_iteratedFiberProduct]
  exact isClosed_setOf_map_eq hπ k

/-- When `M` is Hausdorff and `π` is continuous, the subtype inclusion of
`IteratedFiberProduct π k` into `Fin k → Y` is a closed topological embedding. -/
theorem isClosedEmbedding_coe_iteratedFiberProduct [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosedEmbedding (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) :=
  .subtypeVal (isClosed_setOf_map_eq hπ k)

end Topology

section Manifold

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω}

private theorem tangentSpaceCast_trans {a b c : M} :
    a = b → b = c → ∀ z : TangentSpace IM a,
      tangentSpaceCast IM b c (tangentSpaceCast IM a b z) = tangentSpaceCast IM a c z := by
  rintro rfl rfl _
  rfl

private theorem tangentSpaceCast_self {a : M} (z : TangentSpace IM a) :
    tangentSpaceCast IM a a z = z :=
  rfl

private def piFinOneInvDiffeomorph :
    Y ≃ₘ^n⟮IY, ModelWithCorners.pi (fun _ : Fin 1 ↦ IY)⟯ (Fin 1 → Y) where
  toFun z _ := z
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := funext fun i ↦ by rw [Fin.eq_zero i]
  contMDiff_toFun := contMDiff_pi_iff.2 fun _ ↦ contMDiff_id
  contMDiff_invFun := contMDiff_apply (i := 0)

@[simp]
private theorem piFinOneInvDiffeomorph_apply (z : Y) (i : Fin 1) :
    piFinOneInvDiffeomorph (IY := IY) (n := n) z i = z := rfl

private def piSnocDiffeomorph (m : ℕ) :
    ((Fin (m + 1) → Y) × Y) ≃ₘ^n⟮
      (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY).prod IY,
      ModelWithCorners.pi fun _ : Fin (m + 2) ↦ IY⟯ (Fin (m + 2) → Y) where
  toFun p := Fin.snoc (α := fun _ ↦ Y) p.1 p.2
  invFun g := (Fin.init g, g (Fin.last (m + 1)))
  left_inv p := by ext <;> simp
  right_inv g := Fin.snoc_init_self g
  contMDiff_toFun := contMDiff_pi_iff.2 fun i ↦ i.lastCases
    (by
      change ContMDiff _ _ _ (fun p : (Fin (m + 1) → Y) × Y ↦
        Fin.snoc (α := fun _ ↦ Y) p.1 p.2 (Fin.last (m + 1)))
      simp only [Fin.snoc_last]
      exact contMDiff_snd)
    (fun k ↦ by
      change ContMDiff _ _ _ (fun p : (Fin (m + 1) → Y) × Y ↦
        Fin.snoc (α := fun _ ↦ Y) p.1 p.2 k.castSucc)
      simp only [Fin.snoc_castSucc]
      exact (contMDiff_apply (i := k)).comp contMDiff_fst)
  contMDiff_invFun :=
    (contMDiff_pi_iff.2 fun k ↦ contMDiff_apply (i := k.castSucc)).prodMk
      (contMDiff_apply (i := Fin.last (m + 1)))

@[simp]
private theorem piSnocDiffeomorph_apply (m : ℕ) (p : (Fin (m + 1) → Y) × Y) :
    piSnocDiffeomorph (IY := IY) (Y := Y) (n := n) m p = Fin.snoc (α := fun _ ↦ Y) p.1 p.2 := rfl

private theorem mfderiv_piSnocDiffeomorph_apply [IsManifold IY n Y] (hn : 1 ≤ n) (m : ℕ)
    (p : (Fin (m + 1) → Y) × Y)
    (u : TangentSpace (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) p.1)
    (w : TangentSpace IY p.2) :
    mfderiv ((ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY).prod IY)
      (ModelWithCorners.pi fun _ : Fin (m + 2) ↦ IY)
      (piSnocDiffeomorph (IY := IY) (Y := Y) (n := n) m) p (u, w) =
      Fin.snoc (α := fun _ ↦ EY) u w := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have : IsManifold IY 1 Y := .of_le hn
  let snocD := piSnocDiffeomorph (IY := IY) (Y := Y) (n := n) m
  funext i
  have hcoord := mfderiv_comp (I' := ModelWithCorners.pi fun _ : Fin (m + 2) ↦ IY) p
    (TauCeti.hasMFDerivAt_apply (I := fun _ : Fin (m + 2) ↦ IY) i (snocD p)).mdifferentiableAt
    ((snocD.contMDiff p).mdifferentiableAt hn0)
  rw [TauCeti.mfderiv_apply, Function.comp_def] at hcoord
  let u' : Fin (m + 1) → EY := u
  let w' : EY := w
  have hi : mfderiv ((ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY).prod IY) IY
      (fun q ↦ snocD q i) p (u, w) = Fin.snoc (α := fun _ ↦ EY) u w i := by
    refine i.lastCases ?_ fun k ↦ ?_
    · have hlast_eq : (fun q : (Fin (m + 1) → Y) × Y ↦ snocD q (Fin.last (m + 1))) = Prod.snd :=
        funext fun q ↦ by simp [snocD]
      have h1 : mfderiv ((ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY).prod IY) IY
          (fun q ↦ snocD q (Fin.last (m + 1))) p (u, w) = w' := by
        rw [hlast_eq, mfderiv_snd]
        rfl
      exact h1.trans (Fin.snoc_last (α := fun _ ↦ EY) w u).symm
    · have hcast_eq : (fun q : (Fin (m + 1) → Y) × Y ↦ snocD q k.castSucc) = fun q ↦ q.1 k :=
        funext fun q ↦ by simp [snocD]
      have h1 : mfderiv ((ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY).prod IY) IY
          (fun q ↦ snocD q k.castSucc) p (u, w) = u' k := by
        rw [hcast_eq]
        have hcomp := mfderiv_comp (I' := ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) p
          (TauCeti.hasMFDerivAt_apply (I := fun _ : Fin (m + 1) ↦ IY) k p.1).mdifferentiableAt
          (mdifferentiableAt_fst (I' := IY))
        rw [TauCeti.mfderiv_apply, Function.comp_def, mfderiv_fst] at hcomp
        exact DFunLike.congr_fun hcomp (u, w)
      exact h1.trans (Fin.snoc_castSucc (α := fun _ ↦ EY) w u k).symm
  exact (DFunLike.congr_fun hcoord (u, w)).symm.trans hi

private def iteratedOneHomeomorph {π : Y → M} (hπ : Continuous π) :
    IteratedFiberProduct π 1 ≃ₜ {p : M × Y // id p.1 = π p.2} where
  toFun y := ⟨(π (y.1 0), y.1 0), rfl⟩
  invFun p := ⟨fun _ ↦ p.1.2, fun _ _ ↦ rfl⟩
  left_inv y := Subtype.ext (funext fun i ↦ by rw [Fin.eq_zero i])
  right_inv p := Subtype.ext (Prod.ext p.2.symm rfl)
  continuous_toFun :=
    ((hπ.comp (IteratedFiberProduct.continuous_eval 0)).prodMk
      (IteratedFiberProduct.continuous_eval 0)).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun _ ↦ continuous_subtype_val.snd).subtype_mk _

private def iteratedStepHomeomorph {π : Y → M} (m : ℕ) :
    IteratedFiberProduct π (m + 2) ≃ₜ
      {p : IteratedFiberProduct π (m + 1) × Y // IteratedFiberProduct.baseProj p.1 = π p.2} where
  toFun y := ⟨(⟨Fin.init y.1, fun i j ↦ y.2 i.castSucc j.castSucc⟩, y.1 (Fin.last (m + 1))),
    y.2 0 (Fin.last (m + 1))⟩
  invFun p := ⟨Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2, by
    have hbase : ∀ i : Fin (m + 2),
        π (Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i) = IteratedFiberProduct.baseProj p.1.1 :=
      fun i ↦ i.lastCases
        (by simp only [Fin.snoc_last]; exact p.2.symm)
        (fun k ↦ by simp only [Fin.snoc_castSucc]; exact (p.1.1.2 0 k).symm)
    exact fun i j ↦ (hbase i).trans (hbase j).symm⟩
  left_inv y := Subtype.ext (Fin.snoc_init_self y.1)
  right_inv p := by ext <;> simp
  continuous_toFun :=
    (((continuous_pi fun k : Fin (m + 1) ↦
      IteratedFiberProduct.continuous_eval k.castSucc).subtype_mk _).prodMk
      (IteratedFiberProduct.continuous_eval (Fin.last (m + 1)))).subtype_mk _
  continuous_invFun := by
    refine (continuous_pi fun i ↦ ?_).subtype_mk _
    refine i.lastCases ?_ fun k ↦ ?_
    · change Continuous (fun p :
          {p : IteratedFiberProduct π (m + 1) × Y //
            IteratedFiberProduct.baseProj p.1 = π p.2} ↦
          Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 (Fin.last (m + 1)))
      simp only [Fin.snoc_last]
      exact continuous_subtype_val.snd
    · change Continuous (fun p :
          {p : IteratedFiberProduct π (m + 1) × Y //
            IteratedFiberProduct.baseProj p.1 = π p.2} ↦
          Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 k.castSucc)
      simp only [Fin.snoc_castSucc]
      exact (IteratedFiberProduct.continuous_eval k).comp continuous_subtype_val.fst

/-- Every map `f : X → M` is transverse to a `C^n` submersion `π : Y → M` (`1 ≤ n`) in the
second factor. -/
theorem transverse_of_isSubmersion_right {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {f : X → M} {π : Y → M} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    (p : X × Y) :
    (mfderiv IX IM f p.1).range ⊔
      (((tangentSpaceCast IM (π p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IM π p.2)).range = ⊤ := by
  have hs := (tangentSpaceCast IM (π p.2) (f p.1)).surjective.comp
    (hπ.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)) p.2)
  have hr : (((tangentSpaceCast IM (π p.2) (f p.1)).toContinuousLinearMap).comp
      (mfderiv IY IM π p.2)).range = ⊤ := LinearMap.range_eq_top.2 hs
  rw [hr, sup_top_eq]

private theorem iter_dim_succ (m a b : ℕ) :
    (m + 1) * a - m * b + a - b = (m + 2) * a - (m + 1) * b := by
  rw [Nat.succ_mul (m + 1) a, Nat.succ_mul m b]
  rcases le_or_gt (m * b) ((m + 1) * a) with h | h
  · rw [← Nat.sub_add_comm h, Nat.sub_sub]
  · have hab : a < b := lt_of_not_ge fun hba ↦ by
      have hmba : m * b ≤ m * a := Nat.mul_le_mul_left m hba
      rw [Nat.succ_mul m a] at h
      omega
    omega

variable [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]

/-- **Local projection normal form for `IteratedFiberProduct`.** Around every point
`y : IteratedFiberProduct π (m + 1)`, there exist maximal-atlas charts `φ i` of `Y` around `y.1 i`
(whose product `OpenPartialHomeomorph.pi φ` belongs to the maximal atlas of `Fin (m + 1) → Y`) and
linear splittings `L i : EY ≃L[ℝ] EM × (Fin (dim Y - dim M) → ℝ)` over `extChartAt IM (baseProj y)`
such that, on `(OpenPartialHomeomorph.pi φ).source`, a tuple `z : Fin (m + 1) → Y` belongs to
`IteratedFiberProduct π (m + 1)` if and only if all its base-projection coordinates
`(L i ((φ i).extend IY (z i))).1` agree. The base `M` is not required to be boundaryless. -/
theorem exists_submersionCharts_iteratedFiberProduct {π : Y → M} (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ}
    (y : IteratedFiberProduct π (m + 1)) :
    ∃ (φ : ∀ _ : Fin (m + 1), OpenPartialHomeomorph Y HY)
      (L : ∀ _ : Fin (m + 1), EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)),
      y.1 ∈ (OpenPartialHomeomorph.pi φ).source ∧
      OpenPartialHomeomorph.pi φ ∈
        IsManifold.maximalAtlas (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) n
          (Fin (m + 1) → Y) ∧
      (∀ i (w : Y), w ∈ (φ i).source →
        extChartAt IM (IteratedFiberProduct.baseProj y) (π w) =
          (L i ((φ i).extend IY w)).1) ∧
      ∀ z ∈ (OpenPartialHomeomorph.pi φ).source,
        (z ∈ range (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) ↔
          ∀ i j : Fin (m + 1),
            (L i ((φ i).extend IY (z i))).1 = (L j ((φ j).extend IY (z j))).1) := by
  have hchart : ∀ i : Fin (m + 1),
      ∃ (φ_i : OpenPartialHomeomorph Y HY)
        (L_i : EY ≃L[ℝ] EM × (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)),
        y.1 i ∈ φ_i.source ∧ φ_i ∈ IsManifold.maximalAtlas IY n Y ∧
        φ_i.source ⊆ π ⁻¹' (chartAt HM (IteratedFiberProduct.baseProj y)).source ∧
        ∀ w ∈ φ_i.source,
          extChartAt IM (IteratedFiberProduct.baseProj y) (π w) = (L_i (φ_i.extend IY w)).1 := by
    intro i
    simpa only [← IteratedFiberProduct.baseProj_eq_apply y i] using
      hπ.exists_domChart_mem_maximalAtlas_chartAt hn (y.1 i)
  choose φ L hyφ hφmax hφsub hφeq using hchart
  refine ⟨φ, L, fun i _ ↦ hyφ i, TauCeti.pi_mem_maximalAtlas hφmax, hφeq, fun z hz ↦ ?_⟩
  rw [mem_range_coe_iteratedFiberProduct_iff]
  have hzeq : ∀ i : Fin (m + 1),
      (L i ((φ i).extend IY (z i))).1 =
        extChartAt IM (IteratedFiberProduct.baseProj y) (π (z i)) :=
    fun i ↦ (hφeq i (z i) (hz i trivial)).symm
  have hzmem : ∀ i : Fin (m + 1),
      π (z i) ∈ (extChartAt IM (IteratedFiberProduct.baseProj y)).source := by
    intro i
    rw [extChartAt_source]
    exact hφsub i (hz i trivial)
  refine ⟨fun h i j ↦ by rw [hzeq i, hzeq j, h i j], fun h i j ↦ ?_⟩
  have hinj := h i j
  rw [hzeq i, hzeq j] at hinj
  exact (extChartAt IM (IteratedFiberProduct.baseProj y)).injOn (hzmem i) (hzmem j) hinj

variable [IM.Boundaryless]

/-- **Manifold structure and smooth embedding of iterated submersion fibre products.** For a `C^n`
submersion `π : Y → M` (`1 ≤ n`) between finite-dimensional boundaryless real manifolds, the
`(m + 1)`-fold fibre product `IteratedFiberProduct π (m + 1)` carries a `C^n` manifold structure
of dimension `(m + 1) * dim Y - m * dim M` with its subspace topology, smoothly embedded into
`Fin (m + 1) → Y`, whose tangent image consists of tuples of tangent vectors with equal images
under `mfderiv IY IM π`. -/
theorem exists_isManifold_iteratedFiberProduct_isSmoothEmbedding {π : Y → M}
    (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π) (m : ℕ) :
    ∃ cs : ChartedSpace (Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (m + 1)),
      letI := cs
      IsManifold 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
        (IteratedFiberProduct π (m + 1)) ∧
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) n
        (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) ∧
      ∀ (y : IteratedFiberProduct π (m + 1))
        (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) y.1),
        v ∈ (mfderiv
          𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) y).range ↔
        ∀ i j : Fin (m + 1),
          mfderiv IY IM π (y.1 i) (v i) =
            tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have : IsManifold IY 1 Y := .of_le hn
  induction m with
  | zero =>
    let d₀ := finrank ℝ EM + finrank ℝ EY - finrank ℝ EM
    have hd₀ : d₀ = (0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM := by omega
    rw [← hd₀]
    let := transverseFiberProductChartedSpace hn (contMDiff_id (I := IM)) hπ.contMDiff
      (fun p _ ↦ transverse_id_left π p)
    have := isManifold_transverseFiberProduct hn (contMDiff_id (I := IM)) hπ.contMDiff
      (fun p _ ↦ transverse_id_left π p)
    let e₀ := iteratedOneHomeomorph hπ.contMDiff.continuous
    let := e₀.pullbackChartedSpace (H := Fin d₀ → ℝ)
    have := e₀.pullback_isManifold 𝓘(ℝ, Fin d₀ → ℝ) n
    let Φ : IteratedFiberProduct π 1 ≃ₘ^n⟮𝓘(ℝ, Fin d₀ → ℝ),
        ModelWithCorners.pi (fun _ : Fin 1 ↦ IY)⟯ (Fin 1 → Y) :=
      ((e₀.pullbackDiffeomorph 𝓘(ℝ, Fin d₀ → ℝ) n).trans
        (transverseFiberProductIdLeftDiffeomorph hn hπ.contMDiff)).trans
        (piFinOneInvDiffeomorph (IY := IY) (n := n))
    have hΦcoe : (Φ : IteratedFiberProduct π 1 → (Fin 1 → Y)) = Subtype.val := by
      funext y; funext i
      rw [Fin.eq_zero i]
      simp only [Φ, Diffeomorph.coe_trans, Function.comp_apply, piFinOneInvDiffeomorph_apply,
        Homeomorph.coe_pullbackDiffeomorph]
      exact transverseFiberProductIdLeftDiffeomorph_apply hn hπ.contMDiff (e₀ y)
    have himm : Manifold.IsImmersion 𝓘(ℝ, Fin d₀ → ℝ)
        (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) n
        (Subtype.val : IteratedFiberProduct π 1 → (Fin 1 → Y)) := by
      have hcomp : (Subtype.val : IteratedFiberProduct π 1 → (Fin 1 → Y)) = Φ ∘ id := by
        rw [comp_id, hΦcoe]
      rw [hcomp]
      exact Φ.isImmersion_comp hn Manifold.IsImmersion.id
    refine ⟨inferInstance, inferInstance, ⟨himm, IsEmbedding.subtypeVal⟩, fun y v ↦ ?_⟩
    rw [← hΦcoe]
    refine ⟨fun _ i j ↦ ?_, fun _ ↦ ?_⟩
    · rw [Fin.eq_zero i, Fin.eq_zero j]
      rfl
    · exact (Φ.isInvertible_mfderiv hn0).surjective v
  | succ m ih =>
    obtain ⟨cs_m, hman_m, hemb_m, hrange_m⟩ := ih
    let := cs_m
    let d_m := (m + 1) * finrank ℝ EY - m * finrank ℝ EM
    let K_m := 𝓘(ℝ, Fin d_m → ℝ)
    let PI_m := ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY
    let PI_succ := ModelWithCorners.pi fun _ : Fin (m + 2) ↦ IY
    have hf : ContMDiff K_m IM n
        (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 1) → M) :=
      hπ.contMDiff.comp ((contMDiff_apply (i := (0 : Fin (m + 1)))).comp hemb_m.contMDiff)
    have htrans : ∀ p : IteratedFiberProduct π (m + 1) × Y,
        IteratedFiberProduct.baseProj p.1 = π p.2 →
        (mfderiv K_m IM IteratedFiberProduct.baseProj p.1).range ⊔
          (((tangentSpaceCast IM (π p.2)
            (IteratedFiberProduct.baseProj p.1)).toContinuousLinearMap).comp
              (mfderiv IY IM π p.2)).range = ⊤ :=
      fun p _ ↦ transverse_of_isSubmersion_right hn hπ p
    let Q := {p : IteratedFiberProduct π (m + 1) × Y //
      IteratedFiberProduct.baseProj p.1 = π p.2}
    let d' := finrank ℝ (Fin d_m → ℝ) + finrank ℝ EY - finrank ℝ EM
    have hd' : d' = (m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM := by
      dsimp only [d', d_m]
      rw [Module.finrank_fin_fun]
      exact iter_dim_succ m (finrank ℝ EY) (finrank ℝ EM)
    rw [← hd']
    let := transverseFiberProductChartedSpace hn hf hπ.contMDiff htrans
    have := isManifold_transverseFiberProduct hn hf hπ.contMDiff htrans
    have hemb_Q := isSmoothEmbedding_coe_transverseFiberProduct hn hf hπ.contMDiff htrans
    have hrange_Q := mem_range_mfderiv_coe_transverseFiberProduct_iff hn hf hπ.contMDiff htrans
    let e_step := iteratedStepHomeomorph (π := π) m
    let := e_step.pullbackChartedSpace (H := Fin d' → ℝ)
    have := e_step.pullback_isManifold 𝓘(ℝ, Fin d' → ℝ) n
    let ψ := e_step.pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
    have hψ_coe : (ψ : IteratedFiberProduct π (m + 2) → Q) = e_step :=
      Homeomorph.coe_pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n e_step
    have he_step_cont : ContMDiff 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) n e_step :=
      hψ_coe ▸ ψ.contMDiff
    have he_step_inv : ∀ y : IteratedFiberProduct π (m + 2),
        (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y).IsInvertible := fun y ↦ by
      rw [← hψ_coe]
      exact ψ.isInvertible_mfderiv hn0
    let snocD := piSnocDiffeomorph (IY := IY) (Y := Y) (n := n) m
    have hfactor : (Subtype.val : IteratedFiberProduct π (m + 2) → (Fin (m + 2) → Y)) =
        snocD ∘ Prod.map Subtype.val id ∘ (Subtype.val : Q → _) ∘ e_step := by
      funext y
      simp only [Function.comp_apply, snocD, piSnocDiffeomorph_apply]
      exact (Fin.snoc_init_self y.1).symm
    have hcont_coe : ContMDiff 𝓘(ℝ, Fin d' → ℝ) PI_succ n
        (Subtype.val : IteratedFiberProduct π (m + 2) → (Fin (m + 2) → Y)) := by
      rw [hfactor]
      exact snocD.contMDiff.comp ((hemb_m.contMDiff.prodMap contMDiff_id).comp
        (hemb_Q.contMDiff.comp he_step_cont))
    -- Compute the differential of `Subtype.val` along the four-step factorization.
    have hmf_coe : ∀ (y : IteratedFiberProduct π (m + 2))
        (ξ : TangentSpace 𝓘(ℝ, Fin d' → ℝ) y),
        mfderiv 𝓘(ℝ, Fin d' → ℝ) PI_succ Subtype.val y ξ =
          Fin.snoc (α := fun _ ↦ EY)
            (mfderiv K_m PI_m Subtype.val (e_step y).1.1
              (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
                (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ)).1)
            (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
              (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ)).2 := by
      intro y ξ
      have : IsManifold K_m 1 (IteratedFiberProduct π (m + 1)) := .of_le hn
      let q : Q := e_step y
      have hed := (he_step_cont y).mdifferentiableAt hn0
      have hQd := (hemb_Q.contMDiff q).mdifferentiableAt hn0
      have hmd := ((hemb_m.contMDiff.prodMap (contMDiff_id (I := IY))) q.1).mdifferentiableAt
        hn0
      have hsnocd := (snocD.contMDiff (q.1.1.1, q.1.2)).mdifferentiableAt hn0
      have hc_Qe := mfderiv_comp y hQd hed
      have hc_mQe := mfderiv_comp y hmd (hQd.comp y hed)
      have hc_all := mfderiv_comp y hsnocd (hmd.comp y (hQd.comp y hed))
      have hprod : mfderiv (K_m.prod IY) (PI_m.prod IY) (Prod.map Subtype.val id) q.1 =
          (mfderiv K_m PI_m Subtype.val q.1.1).prodMap
            (ContinuousLinearMap.id ℝ (TangentSpace IY q.1.2)) := by
        rw [mfderiv_prodMap (p := q.1) ((hemb_m.contMDiff q.1.1).mdifferentiableAt hn0)
          (mdifferentiableAt_id (I := IY)), mfderiv_id]
      have hfactor_mf : mfderiv 𝓘(ℝ, Fin d' → ℝ) PI_succ
          (Subtype.val : IteratedFiberProduct π (m + 2) → (Fin (m + 2) → Y)) y =
          mfderiv 𝓘(ℝ, Fin d' → ℝ) PI_succ
            (snocD ∘ Prod.map Subtype.val id ∘ (Subtype.val : Q → _) ∘ e_step) y := by
        rw [hfactor]
      have hc1 : mfderiv 𝓘(ℝ, Fin d' → ℝ) PI_succ
          (Subtype.val : IteratedFiberProduct π (m + 2) → (Fin (m + 2) → Y)) y =
          (mfderiv (PI_m.prod IY) PI_succ snocD (q.1.1.1, q.1.2)).comp
            (((mfderiv K_m PI_m Subtype.val q.1.1).prodMap
                (ContinuousLinearMap.id ℝ (TangentSpace IY q.1.2))).comp
              ((mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val q).comp
                (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y))) :=
        hfactor_mf.trans (hc_all.trans
          (congrArg (mfderiv (PI_m.prod IY) PI_succ snocD (q.1.1.1, q.1.2)).comp
            (hc_mQe.trans
              ((congrArg (fun L ↦ L.comp
                  (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) ((Subtype.val : Q → _) ∘ e_step) y))
                hprod).trans
                (congrArg ((mfderiv K_m PI_m Subtype.val q.1.1).prodMap
                  (ContinuousLinearMap.id ℝ (TangentSpace IY q.1.2))).comp hc_Qe)))))
      exact (DFunLike.congr_fun hc1 ξ).trans
        (mfderiv_piSnocDiffeomorph_apply hn m (q.1.1.1, q.1.2) _ _)
    have himm : Manifold.IsImmersion 𝓘(ℝ, Fin d' → ℝ) PI_succ n
        (Subtype.val : IteratedFiberProduct π (m + 2) → (Fin (m + 2) → Y)) := by
      refine hcont_coe.isImmersion_of_injective_mfderiv hn fun y ξ₁ ξ₂ hξ ↦ ?_
      have hsnoc := (hmf_coe y ξ₁).symm.trans (hξ.trans (hmf_coe y ξ₂))
      have hinit : mfderiv K_m PI_m Subtype.val (e_step y).1.1
          (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
            (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ₁)).1 =
        mfderiv K_m PI_m Subtype.val (e_step y).1.1
          (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
            (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ₂)).1 :=
        funext fun k ↦
          (Fin.snoc_castSucc (α := fun _ ↦ EY) _ _ k).symm.trans
            ((congrFun hsnoc k.castSucc).trans (Fin.snoc_castSucc (α := fun _ ↦ EY) _ _ k))
      have hlast :=
        (Fin.snoc_last (α := fun _ ↦ EY) _ _).symm.trans
          ((congrFun hsnoc (Fin.last (m + 1))).trans (Fin.snoc_last (α := fun _ ↦ EY) _ _))
      have h1 := (hemb_m.isImmersion.isImmersionAt (e_step y).1.1).mfderiv_injective hn0 hinit
      have hpair := Prod.ext h1 hlast
      have hQ := (hemb_Q.isImmersion.isImmersionAt (e_step y)).mfderiv_injective hn0 hpair
      exact (he_step_inv y).injective hQ
    refine ⟨inferInstance, inferInstance, ⟨himm, IsEmbedding.subtypeVal⟩, fun y v ↦ ?_⟩
    -- Identify the differential of `baseProj` at `p₁ = (e_step y).1.1` through the `0`-th factor.
    let p₁ : IteratedFiberProduct π (m + 1) := (e_step y).1.1
    have hmf_base : ∀ ζ : TangentSpace K_m p₁,
        mfderiv K_m IM IteratedFiberProduct.baseProj p₁ ζ =
          mfderiv IY IM π (y.1 0)
            ((mfderiv K_m PI_m Subtype.val p₁ ζ : Fin (m + 1) → EY) 0) := by
      intro ζ
      have heval0 : MDifferentiableAt PI_m IY (fun f : Fin (m + 1) → Y ↦ f 0) p₁.1 :=
        (TauCeti.hasMFDerivAt_apply (I := fun _ : Fin (m + 1) ↦ IY)
          (0 : Fin (m + 1)) p₁.1).mdifferentiableAt
      have hc1 := mfderiv_comp p₁
        (((hπ.contMDiff (p₁.1 0)).mdifferentiableAt hn0).comp p₁.1 heval0)
        ((hemb_m.contMDiff p₁).mdifferentiableAt hn0)
      have hc2 := mfderiv_comp p₁.1 ((hπ.contMDiff (p₁.1 0)).mdifferentiableAt hn0) heval0
      rw [TauCeti.mfderiv_apply] at hc2
      exact DFunLike.congr_fun
        (hc1.trans (congrArg (·.comp (mfderiv K_m PI_m Subtype.val p₁)) hc2)) ζ
    constructor
    · rintro ⟨ξ, hξ⟩
      let η := mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ
      let pair := mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y) η
      let u : Fin (m + 1) → EY := mfderiv K_m PI_m Subtype.val p₁ pair.1
      have hv_eq : v = Fin.snoc (α := fun _ ↦ EY) u pair.2 :=
        hξ.symm.trans (hmf_coe y ξ)
      have hv_last : v (Fin.last (m + 1)) = pair.2 :=
        (congrFun hv_eq (Fin.last (m + 1))).trans (Fin.snoc_last (α := fun _ ↦ EY) pair.2 u)
      have hv_cast : ∀ k : Fin (m + 1), v k.castSucc = u k := fun k ↦
        (congrFun hv_eq k.castSucc).trans (Fin.snoc_castSucc (α := fun _ ↦ EY) pair.2 u k)
      have hQmem : mfderiv IY IM π (y.1 0) (u 0) =
          tangentSpaceCast IM (π (y.1 (Fin.last (m + 1)))) (IteratedFiberProduct.baseProj p₁)
            (mfderiv IY IM π (y.1 (Fin.last (m + 1))) pair.2) :=
        (hmf_base pair.1).symm.trans ((hrange_Q (e_step y) pair).1 ⟨η, rfl⟩)
      have humem : ∀ i j : Fin (m + 1),
          mfderiv IY IM π (p₁.1 i) (u i) =
            tangentSpaceCast IM (π (p₁.1 j)) (π (p₁.1 i)) (mfderiv IY IM π (p₁.1 j) (u j)) :=
        (hrange_m p₁ u).1 ⟨pair.1, rfl⟩
      -- Every coordinate agrees with coordinate `0` after transporting to `π (y.1 0)`.
      have h0 : ∀ i : Fin (m + 2),
          tangentSpaceCast IM (π (y.1 i)) (π (y.1 0))
            (mfderiv IY IM π (y.1 i) (v i)) =
            mfderiv IY IM π (y.1 0) (u 0) := by
        intro i
        refine i.lastCases ?_ fun k ↦ ?_
        · exact (congrArg (fun z ↦
            tangentSpaceCast IM (π (y.1 (Fin.last (m + 1)))) (π (y.1 0))
              (mfderiv IY IM π (y.1 (Fin.last (m + 1))) z)) hv_last).trans hQmem.symm
        · exact (congrArg (fun z ↦
            tangentSpaceCast IM (π (y.1 k.castSucc)) (π (y.1 0))
              (mfderiv IY IM π (y.1 k.castSucc) z)) (hv_cast k)).trans (humem 0 k).symm
      intro i j
      -- Transport both equalities from `π (y.1 0)` to `π (y.1 i)` along the common base point.
      have h1 : mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 0)) (π (y.1 i))
            (tangentSpaceCast IM (π (y.1 i)) (π (y.1 0))
              (mfderiv IY IM π (y.1 i) (v i))) :=
        (tangentSpaceCast_trans (y.2 i 0) (y.2 0 i) _).symm
      have h2 : tangentSpaceCast IM (π (y.1 0)) (π (y.1 i))
            (tangentSpaceCast IM (π (y.1 i)) (π (y.1 0))
              (mfderiv IY IM π (y.1 i) (v i))) =
          tangentSpaceCast IM (π (y.1 0)) (π (y.1 i))
            (tangentSpaceCast IM (π (y.1 j)) (π (y.1 0))
              (mfderiv IY IM π (y.1 j) (v j))) :=
        congrArg (tangentSpaceCast IM (π (y.1 0)) (π (y.1 i))) ((h0 i).trans (h0 j).symm)
      exact h1.trans (h2.trans (tangentSpaceCast_trans (y.2 j 0) (y.2 0 i) _))
    · intro hv
      obtain ⟨ζ, hζ⟩ := (hrange_m p₁ (Fin.init v)).2 fun i j ↦ hv i.castSucc j.castSucc
      change mfderiv K_m PI_m Subtype.val p₁ ζ = Fin.init v at hζ
      have hζ0 : (mfderiv K_m PI_m Subtype.val p₁ ζ : Fin (m + 1) → EY) 0 = v 0 :=
        congrFun hζ 0
      have hQcond : mfderiv K_m IM IteratedFiberProduct.baseProj p₁ ζ =
          tangentSpaceCast IM (π (y.1 (Fin.last (m + 1)))) (IteratedFiberProduct.baseProj p₁)
            (mfderiv IY IM π (y.1 (Fin.last (m + 1))) (v (Fin.last (m + 1)))) :=
        (hmf_base ζ).trans ((congrArg (mfderiv IY IM π (y.1 0)) hζ0).trans
          (hv 0 (Fin.last (m + 1))))
      obtain ⟨η, hη⟩ := (hrange_Q (e_step y) (ζ, v (Fin.last (m + 1)))).2 hQcond
      change mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y) η =
        (ζ, v (Fin.last (m + 1))) at hη
      obtain ⟨ξ, hξ⟩ := (he_step_inv y).surjective η
      have hpair_eq : mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
          (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ) =
          (ζ, v (Fin.last (m + 1))) :=
        (congrArg (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)) hξ).trans hη
      have hu_eq : mfderiv K_m PI_m Subtype.val (e_step y).1.1
          (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
            (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ)).1 = Fin.init v :=
        (congrArg (mfderiv K_m PI_m Subtype.val (e_step y).1.1)
          (congrArg Prod.fst hpair_eq)).trans hζ
      have hw_eq : (mfderiv 𝓘(ℝ, Fin d' → ℝ) (K_m.prod IY) Subtype.val (e_step y)
          (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e_step y ξ)).2 =
          v (Fin.last (m + 1)) :=
        congrArg Prod.snd hpair_eq
      refine ⟨ξ, (hmf_coe y ξ).trans (funext fun i ↦ ?_)⟩
      refine i.lastCases ?_ fun k ↦ ?_
      · exact (Fin.snoc_last (α := fun _ ↦ EY) _ _).trans hw_eq
      · exact (Fin.snoc_castSucc (α := fun _ ↦ EY) _ _ k).trans (congrFun hu_eq k)

section ChosenAtlas

variable {π : Y → M} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- The canonical `C^n` atlas on `IteratedFiberProduct π (m + 1)`, constructed by iterating
`TauCeti.transverseFiberProductChartedSpace` along `IteratedFiberProduct.baseProj` and `π`. It uses
the subspace topology inherited from `Fin (m + 1) → Y` and is a named definition rather than a
global instance. -/
@[instance_reducible]
noncomputable def iteratedFiberProductChartedSpace (m : ℕ) :
    ChartedSpace (Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π (m + 1)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ m).choose

/-- With its chosen atlas, `IteratedFiberProduct π (m + 1)` is a `C^n` manifold of dimension
`(m + 1) * dim Y - m * dim M`. -/
theorem isManifold_iteratedFiberProduct (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    IsManifold 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct π (m + 1)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ m).choose_spec.1

/-- With its chosen atlas, the inclusion of `IteratedFiberProduct π (m + 1)` into `Fin (m + 1) → Y`
is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_coe_iteratedFiberProduct (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ m).choose_spec.2.1

/-- A tangent tuple in `Fin (m + 1) → Y` lies in the tangent image of
`IteratedFiberProduct π (m + 1)` if and only if all its coordinates have equal images under
`mfderiv IY IM π`. -/
theorem mem_range_mfderiv_coe_iteratedFiberProduct_iff (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ∀ (y : IteratedFiberProduct π (m + 1))
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) y.1),
      v ∈ (mfderiv
        𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (m + 1) → (Fin (m + 1) → Y)) y).range ↔
      ∀ i j : Fin (m + 1),
        mfderiv IY IM π (y.1 i) (v i) =
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) :=
  (exists_isManifold_iteratedFiberProduct_isSmoothEmbedding hn hπ m).choose_spec.2.2

/-- **Smooth universal property of `IteratedFiberProduct`.** For `m' ≤ n`, a map into
`IteratedFiberProduct π (m + 1)` is `C^{m'}` if and only if each coordinate map into `Y` is
`C^{m'}`. No separate continuity assumption is required. -/
theorem contMDiff_iteratedFiberProduct_iff {EX HX X : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) {f : X → IteratedFiberProduct π (m + 1)} :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff IX 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) m' f ↔
      ∀ i : Fin (m + 1), ContMDiff IX IY m' (fun x ↦ IteratedFiberProduct.eval i (f x)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  rw [((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m).of_le hm').contMDiff_iff_comp,
    contMDiff_pi_iff]
  rfl

/-- Every factor projection `eval i : Y^[m + 1] → Y` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_eval {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY m'
      (IteratedFiberProduct.eval i : IteratedFiberProduct π (m + 1) → Y) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  exact (contMDiff_apply (i := i)).comp
    ((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m).contMDiff.of_le hm')

/-- The diagonal map `const (m + 1) : Y → Y^[m + 1]` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_const {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff IY 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) m'
      (IteratedFiberProduct.const (π := π) (m + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  exact (contMDiff_iteratedFiberProduct_iff hn hπ hm').2 fun _ ↦ contMDiff_id

/-- The base projection `baseProj : Y^[m + 1] → M` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_baseProj {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IM m'
      (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 1) → M) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  exact (hπ.contMDiff.of_le hm').comp (contMDiff_eval hn hπ hm' 0)

/-- The differential of `eval i` at `y` is the `i`-th coordinate of the differential of
`Subtype.val`. -/
theorem mfderiv_eval_apply {m : ℕ} (y : IteratedFiberProduct π (m + 1)) (i : Fin (m + 1))
    (ξ : letI := iteratedFiberProductChartedSpace hn hπ m
      TangentSpace 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) y) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY
      (IteratedFiberProduct.eval i) y ξ =
      mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) Subtype.val y ξ i := by
  let := iteratedFiberProductChartedSpace hn hπ m
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hcomp := mfderiv_comp y (TauCeti.hasMFDerivAt_apply i y.1).mdifferentiableAt
    (((isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m).contMDiff y).mdifferentiableAt hn0)
  rw [TauCeti.mfderiv_apply] at hcomp
  exact DFunLike.congr_fun hcomp ξ

/-- Every family of tangent vectors `(v i)` along `y : IteratedFiberProduct π (m + 1)` with equal
images under `mfderiv IY IM π` arises from a tangent vector `ξ` of `IteratedFiberProduct π (m + 1)`
under the differentials of `eval i`. -/
theorem exists_mfderiv_eval_eq_of_iteratedFiberProduct {m : ℕ}
    (y : IteratedFiberProduct π (m + 1)) (v : ∀ i : Fin (m + 1), TangentSpace IY (y.1 i))
    (hv : ∀ i j : Fin (m + 1),
      mfderiv IY IM π (y.1 i) (v i) =
        tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j))) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ∃ ξ, ∀ i : Fin (m + 1),
      mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY
        (IteratedFiberProduct.eval i) y ξ = v i := by
  let := iteratedFiberProductChartedSpace hn hπ m
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ m y v).2 hv
  exact ⟨ξ, fun i ↦ (mfderiv_eval_apply hn hπ y i ξ).trans (congrFun hξ i)⟩

/-- A tangent vector of `IteratedFiberProduct π (m + 1)` is zero when the differentials of all
factor projections `eval i` vanish on it. -/
theorem eq_zero_of_mfderiv_eval_iteratedFiberProduct {m : ℕ}
    (y : IteratedFiberProduct π (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    ∀ ξ : TangentSpace 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) y,
      (∀ i : Fin (m + 1),
        mfderiv 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY
          (IteratedFiberProduct.eval i) y ξ = 0) →
      ξ = 0 := by
  let := iteratedFiberProductChartedSpace hn hπ m
  intro ξ hξ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hi := isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m
  refine (injective_iff_map_eq_zero _).1 ((hi.isImmersion.isImmersionAt y).mfderiv_injective hn0)
    ξ (funext fun i ↦ ?_)
  exact (mfderiv_eval_apply hn hπ y i ξ).symm.trans (hξ i)

/-- **The composite base projection is a submersion.** On `IteratedFiberProduct π (m + 1)`,
`IteratedFiberProduct.baseProj : Y^[m + 1] → M` is a `C^n` submersion. -/
theorem isSubmersion_baseProj (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IM n
      (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 1) → M) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  have := isManifold_iteratedFiberProduct hn hπ m
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_baseProj hn hπ le_rfl).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun y w ↦ ?_).isSubmersion
  have hsurj : ∀ i : Fin (m + 1),
      ∃ u : TangentSpace IY (y.1 i),
        tangentSpaceCast IM (π (y.1 i)) (IteratedFiberProduct.baseProj y)
          (mfderiv IY IM π (y.1 i) u) = w :=
    fun i ↦ ((tangentSpaceCast IM (π (y.1 i)) (IteratedFiberProduct.baseProj y)).surjective.comp
      (hπ.surjective_mfderiv hn0 (y.1 i))) w
  choose v hv using hsurj
  have hcompat : ∀ i j : Fin (m + 1),
      mfderiv IY IM π (y.1 i) (v i) =
        tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) := by
    intro i j
    have hyi : π (y.1 i) = IteratedFiberProduct.baseProj y := y.2 i 0
    have hyj : π (y.1 j) = IteratedFiberProduct.baseProj y := y.2 j 0
    calc mfderiv IY IM π (y.1 i) (v i)
        = tangentSpaceCast IM (IteratedFiberProduct.baseProj y) (π (y.1 i))
            (tangentSpaceCast IM (π (y.1 i)) (IteratedFiberProduct.baseProj y)
              (mfderiv IY IM π (y.1 i) (v i))) := by
          rw [tangentSpaceCast_trans hyi hyi.symm, tangentSpaceCast_self]
      _ = tangentSpaceCast IM (IteratedFiberProduct.baseProj y) (π (y.1 i))
            (tangentSpaceCast IM (π (y.1 j)) (IteratedFiberProduct.baseProj y)
              (mfderiv IY IM π (y.1 j) (v j))) := by
          rw [hv i, hv j]
      _ = tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) (v j)) :=
          tangentSpaceCast_trans hyj hyi.symm _
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_eval_eq_of_iteratedFiberProduct hn hπ y v hcompat
  refine ⟨ξ, ?_⟩
  have hbase_eq : (IteratedFiberProduct.baseProj : IteratedFiberProduct π (m + 1) → M) =
      π ∘ IteratedFiberProduct.eval 0 := rfl
  have hc := mfderiv_comp y ((hπ.contMDiff (y.1 0)).mdifferentiableAt hn0)
    (((contMDiff_eval hn hπ le_rfl 0) y).mdifferentiableAt hn0)
  rw [hbase_eq, hc, ContinuousLinearMap.comp_apply, hξ 0]
  exact hv 0

/-- **Every factor projection is a surjective submersion.** On `IteratedFiberProduct π (m + 1)`,
each coordinate projection `eval i : Y^[m + 1] → Y` is a `C^n` submersion. -/
theorem isSubmersion_eval {m : ℕ} (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) IY n
      (IteratedFiberProduct.eval i : IteratedFiberProduct π (m + 1) → Y) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  have := isManifold_iteratedFiberProduct hn hπ m
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_eval hn hπ le_rfl i).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun y u ↦ ?_).isSubmersion
  let w₀ : TangentSpace IM (π (y.1 i)) := mfderiv IY IM π (y.1 i) u
  have hsurj : ∀ j : Fin (m + 1),
      ∃ v_j : TangentSpace IY (y.1 j),
        (j = i → tangentSpaceCast IY (y.1 j) (y.1 i) v_j = u) ∧
          tangentSpaceCast IM (π (y.1 j)) (π (y.1 i)) (mfderiv IY IM π (y.1 j) v_j) = w₀ := by
    intro j
    by_cases hji : j = i
    · subst hji
      exact ⟨u, fun _ ↦ rfl, rfl⟩
    · obtain ⟨v_j, hv_j⟩ :=
        ((tangentSpaceCast IM (π (y.1 j)) (π (y.1 i))).surjective.comp
          (hπ.surjective_mfderiv hn0 (y.1 j))) w₀
      exact ⟨v_j, fun h ↦ (hji h).elim, hv_j⟩
  choose v hv_eq hv_map using hsurj
  have hcompat : ∀ j₁ j₂ : Fin (m + 1),
      mfderiv IY IM π (y.1 j₁) (v j₁) =
        tangentSpaceCast IM (π (y.1 j₂)) (π (y.1 j₁)) (mfderiv IY IM π (y.1 j₂) (v j₂)) := by
    intro j₁ j₂
    calc mfderiv IY IM π (y.1 j₁) (v j₁)
        = tangentSpaceCast IM (π (y.1 i)) (π (y.1 j₁))
            (tangentSpaceCast IM (π (y.1 j₁)) (π (y.1 i))
              (mfderiv IY IM π (y.1 j₁) (v j₁))) := by
          rw [tangentSpaceCast_trans (y.2 j₁ i) (y.2 i j₁), tangentSpaceCast_self]
      _ = tangentSpaceCast IM (π (y.1 i)) (π (y.1 j₁))
            (tangentSpaceCast IM (π (y.1 j₂)) (π (y.1 i))
              (mfderiv IY IM π (y.1 j₂) (v j₂))) := by
          rw [hv_map j₁, hv_map j₂]
      _ = tangentSpaceCast IM (π (y.1 j₂)) (π (y.1 j₁))
            (mfderiv IY IM π (y.1 j₂) (v j₂)) :=
          tangentSpaceCast_trans (y.2 j₂ i) (y.2 i j₁) _
  obtain ⟨ξ, hξ⟩ := exists_mfderiv_eval_eq_of_iteratedFiberProduct hn hπ y v hcompat
  exact ⟨ξ, (hξ i).trans (hv_eq i rfl)⟩

/-! ### Canonical diffeomorphisms for `k = 1`, `k = 2`, and arbitrary splittings -/

/-- The one-fold fibre product `IteratedFiberProduct π 1` is `C^n` diffeomorphic to `Y` via
evaluation at `0`, with inverse `const 1`. -/
noncomputable def iteratedFiberProductOneDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    IteratedFiberProduct π 1 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ), IY⟯ Y := by
  letI := iteratedFiberProductChartedSpace hn hπ 0
  exact
    { toFun := IteratedFiberProduct.eval 0
      invFun := IteratedFiberProduct.const 1
      left_inv := fun y ↦ Subtype.ext (funext fun i ↦ by rw [Fin.eq_zero i]; rfl)
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := contMDiff_eval hn hπ le_rfl 0
      contMDiff_invFun := contMDiff_const hn hπ le_rfl }

/-- `iteratedFiberProductOneDiffeomorph` evaluates at coordinate `0`. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_apply (y : IteratedFiberProduct π 1) :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    iteratedFiberProductOneDiffeomorph hn hπ y = IteratedFiberProduct.eval 0 y := (rfl)

/-- The inverse of `iteratedFiberProductOneDiffeomorph` is the diagonal `const 1`. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_symm_apply (z : Y) :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    (iteratedFiberProductOneDiffeomorph hn hπ).symm z = IteratedFiberProduct.const 1 z := (rfl)

/-- The two-fold fibre product `IteratedFiberProduct π 2` is `C^n` diffeomorphic to the binary
transverse fibre product `{p : Y × Y // π p.1 = π p.2}` via `y ↦ (y₀, y₁)`. -/
noncomputable def iteratedFiberProductTwoDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    IteratedFiberProduct π 2 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((1 + 1) * finrank ℝ EY - 1 * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : Y × Y // π p.1 = π p.2} := by
  letI := iteratedFiberProductChartedSpace hn hπ 1
  letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn hπ.contMDiff hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  refine
    { toFun := fun y ↦ ⟨(IteratedFiberProduct.eval 0 y, IteratedFiberProduct.eval 1 y), y.2 0 1⟩
      invFun := fun p ↦ ⟨![p.1.1, p.1.2], fun i j ↦ by
        fin_cases i <;> fin_cases j <;> simp [p.2]⟩
      left_inv := fun y ↦ Subtype.ext (funext fun i ↦ by fin_cases i <;> rfl)
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := hemb.contMDiff_iff_comp.2
        ((contMDiff_eval hn hπ le_rfl 0).prodMk (contMDiff_eval hn hπ le_rfl 1))
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦ by
        fin_cases i
        · exact hemb.contMDiff.fst
        · exact hemb.contMDiff.snd }

/-- `iteratedFiberProductTwoDiffeomorph` sends `y` to the pair `(eval 0 y, eval 1 y)`. -/
@[simp]
theorem coe_iteratedFiberProductTwoDiffeomorph_apply (y : IteratedFiberProduct π 2) :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    (iteratedFiberProductTwoDiffeomorph hn hπ y : Y × Y) =
      (IteratedFiberProduct.eval 0 y, IteratedFiberProduct.eval 1 y) := (rfl)

/-- The inverse of `iteratedFiberProductTwoDiffeomorph` sends `p` to the two-tuple
`![p.1.1, p.1.2]`. -/
@[simp]
theorem coe_iteratedFiberProductTwoDiffeomorph_symm_apply
    (p : {p : Y × Y // π p.1 = π p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    ((iteratedFiberProductTwoDiffeomorph hn hπ).symm p : Fin 2 → Y) = ![p.1.1, p.1.2] := (rfl)

/-- **Independence of the order of iteration.** Splitting an `(m₁ + m₂ + 2)`-tuple into its first
`m₁ + 1` and last `m₂ + 1` coordinates defines a `C^n` diffeomorphism from
`IteratedFiberProduct π (m₁ + m₂ + 2)` onto the binary transverse fibre product of
`IteratedFiberProduct π (m₁ + 1)` and `IteratedFiberProduct π (m₂ + 1)` over `M`. In particular,
left iteration (`m₁ = 0`), right iteration (`m₂ = 0`), and arbitrary parenthesizations produce
canonically diffeomorphic manifolds. -/
noncomputable def iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
      (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    IteratedFiberProduct π (m₁ + m₂ + 2) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((m₁ + m₂ + 2) * finrank ℝ EY - (m₁ + m₂ + 1) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ) +
        finrank ℝ (Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ) -
        finrank ℝ EM) → ℝ)⟯
      {p : IteratedFiberProduct π (m₁ + 1) × IteratedFiberProduct π (m₂ + 1) //
        IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2} := by
  letI := iteratedFiberProductChartedSpace hn hπ m₁
  letI := iteratedFiberProductChartedSpace hn hπ m₂
  letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
  haveI := isManifold_iteratedFiberProduct hn hπ m₁
  haveI := isManifold_iteratedFiberProduct hn hπ m₂
  letI := transverseFiberProductChartedSpace hn
    (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
    (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
    (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn
    (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
    (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
    (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
  let castEquiv : Fin ((m₁ + 1) + (m₂ + 1)) ≃ Fin (m₁ + m₂ + 2) :=
    finCongr (by omega)
  refine
    { toFun := fun y ↦
        ⟨(⟨fun i ↦ y.1 (castEquiv (Fin.castAdd (m₂ + 1) i)),
            fun i j ↦ y.2 _ _⟩,
          ⟨fun j ↦ y.1 (castEquiv (Fin.natAdd (m₁ + 1) j)),
            fun i j ↦ y.2 _ _⟩),
          y.2 _ _⟩
      invFun := fun p ↦
        ⟨fun k ↦ Fin.append p.1.1.1 p.1.2.1 (castEquiv.symm k), by
          have hbase : ∀ r : Fin ((m₁ + 1) + (m₂ + 1)),
              π (Fin.append p.1.1.1 p.1.2.1 r) = IteratedFiberProduct.baseProj p.1.1 := fun r ↦
            Fin.addCases
              (fun i ↦ by
                rw [Fin.append_left]
                exact (IteratedFiberProduct.baseProj_eq_apply p.1.1 i).symm)
              (fun j ↦ by
                rw [Fin.append_right]
                exact (IteratedFiberProduct.baseProj_eq_apply p.1.2 j).symm.trans p.2.symm) r
          exact fun k₁ k₂ ↦ (hbase _).trans (hbase _).symm⟩
      left_inv := fun y ↦ Subtype.ext (funext fun k ↦ by
        obtain ⟨r, rfl⟩ := castEquiv.surjective k
        dsimp only
        rw [Equiv.symm_apply_apply]
        exact Fin.addCases
          (fun i ↦ by rw [Fin.append_left])
          (fun j ↦ by rw [Fin.append_right]) r)
      right_inv := fun p ↦ by
        apply Subtype.ext
        refine Prod.ext (Subtype.ext (funext fun i ↦ ?_)) (Subtype.ext (funext fun j ↦ ?_))
        · simp only [Equiv.symm_apply_apply, Fin.append_left]
        · simp only [Equiv.symm_apply_apply, Fin.append_right]
      contMDiff_toFun := hemb.contMDiff_iff_comp.2 <|
        ((contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦
          contMDiff_eval hn hπ le_rfl (castEquiv (Fin.castAdd (m₂ + 1) i))).prodMk
        ((contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun j ↦
          contMDiff_eval hn hπ le_rfl (castEquiv (Fin.natAdd (m₁ + 1) j)))
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun k ↦ by
        let S := {p : IteratedFiberProduct π (m₁ + 1) × IteratedFiberProduct π (m₂ + 1) //
          IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2}
        change ContMDiff _ IY n (fun p : S ↦ Fin.append p.1.1.1 p.1.2.1 (castEquiv.symm k))
        refine Fin.addCases
          (motive := fun r ↦ ContMDiff _ IY n (fun p : S ↦ Fin.append p.1.1.1 p.1.2.1 r))
          (fun i ↦ ?_) (fun j ↦ ?_) (castEquiv.symm k)
        · simp only [Fin.append_left]
          exact (contMDiff_eval hn hπ le_rfl i).comp hemb.contMDiff.fst
        · simp only [Fin.append_right]
          exact (contMDiff_eval hn hπ le_rfl j).comp hemb.contMDiff.snd }

/-- The underlying tuple of the first factor of `iteratedFiberProductSplitDiffeomorph` reads the
left block of indices. -/
@[simp]
theorem coe_fst_iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ)
    (y : IteratedFiberProduct π (m₁ + m₂ + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
      (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    ((iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂ y).1.1 : Fin (m₁ + 1) → Y) =
      fun i ↦ y.1 (finCongr (by omega) (Fin.castAdd (m₂ + 1) i)) := (rfl)

/-- The first factor of `iteratedFiberProductSplitDiffeomorph` evaluates at the left block of
indices. -/
theorem eval_fst_iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ)
    (y : IteratedFiberProduct π (m₁ + m₂ + 2)) (i : Fin (m₁ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
      (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    IteratedFiberProduct.eval i (iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂ y).1.1 =
      IteratedFiberProduct.eval (finCongr (by omega) (Fin.castAdd (m₂ + 1) i)) y := (rfl)

/-- The underlying tuple of the second factor of `iteratedFiberProductSplitDiffeomorph` reads the
right block of indices. -/
@[simp]
theorem coe_snd_iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ)
    (y : IteratedFiberProduct π (m₁ + m₂ + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
      (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    ((iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂ y).1.2 : Fin (m₂ + 1) → Y) =
      fun j ↦ y.1 (finCongr (by omega) (Fin.natAdd (m₁ + 1) j)) := (rfl)

/-- The second factor of `iteratedFiberProductSplitDiffeomorph` evaluates at the right block of
indices. -/
theorem eval_snd_iteratedFiberProductSplitDiffeomorph (m₁ m₂ : ℕ)
    (y : IteratedFiberProduct π (m₁ + m₂ + 2)) (j : Fin (m₂ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
      (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    IteratedFiberProduct.eval j (iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂ y).1.2 =
      IteratedFiberProduct.eval (finCongr (by omega) (Fin.natAdd (m₁ + 1) j)) y := (rfl)

/-- The underlying tuple of `(iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂).symm p`
concatenates the two tuples via `Fin.append`. -/
@[simp]
theorem coe_iteratedFiberProductSplitDiffeomorph_symm (m₁ m₂ : ℕ)
    (p : {p : IteratedFiberProduct π (m₁ + 1) × IteratedFiberProduct π (m₂ + 1) //
      IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
      (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    ((iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂).symm p : Fin (m₁ + m₂ + 2) → Y) =
      fun k ↦ Fin.append p.1.1.1 p.1.2.1 ((finCongr (by omega)).symm k) := (rfl)

/-- The inverse of `iteratedFiberProductSplitDiffeomorph` concatenates the two tuples via
`Fin.append`. -/
theorem eval_iteratedFiberProductSplitDiffeomorph_symm (m₁ m₂ : ℕ)
    (p : {p : IteratedFiberProduct π (m₁ + 1) × IteratedFiberProduct π (m₂ + 1) //
      IteratedFiberProduct.baseProj p.1 = IteratedFiberProduct.baseProj p.2})
    (k : Fin (m₁ + m₂ + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ (m₁ + m₂ + 1)
    haveI := isManifold_iteratedFiberProduct hn hπ m₁
    haveI := isManifold_iteratedFiberProduct hn hπ m₂
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ (m := m₁) le_rfl)
      (contMDiff_baseProj hn hπ (m := m₂) le_rfl)
      (fun p _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ m₂) p)
    IteratedFiberProduct.eval k ((iteratedFiberProductSplitDiffeomorph hn hπ m₁ m₂).symm p) =
      Fin.append p.1.1.1 p.1.2.1 ((finCongr (by omega)).symm k) := (rfl)

end ChosenAtlas

/-- For the identity submersion `id : M → M`, every iterated fibre product
`IteratedFiberProduct id (m + 1)` is `C^n` diffeomorphic to `M` of dimension
`(m + 1) * dim M - m * dim M = dim M`. -/
noncomputable def iteratedFiberProductIdDiffeomorph (hn : 1 ≤ n) (m : ℕ) :
    letI := iteratedFiberProductChartedSpace hn
      (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) m
    IteratedFiberProduct (id : M → M) (m + 1) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EM - m * finrank ℝ EM) → ℝ), IM⟯ M := by
  let h_id := Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)
  letI := iteratedFiberProductChartedSpace hn h_id m
  exact
    { toFun := IteratedFiberProduct.baseProj
      invFun := IteratedFiberProduct.const (m + 1)
      left_inv := fun y ↦ Subtype.ext (funext fun i ↦ (y.2 0 i))
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := contMDiff_baseProj hn h_id le_rfl
      contMDiff_invFun := contMDiff_const hn h_id le_rfl }

/-- `iteratedFiberProductIdDiffeomorph` acts by `IteratedFiberProduct.baseProj`. -/
@[simp]
theorem iteratedFiberProductIdDiffeomorph_apply (hn : 1 ≤ n) (m : ℕ)
    (y : IteratedFiberProduct (id : M → M) (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn
      (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) m
    iteratedFiberProductIdDiffeomorph (IM := IM) hn m y =
      IteratedFiberProduct.baseProj y := (rfl)

/-- The inverse of `iteratedFiberProductIdDiffeomorph` is the constant diagonal `const (m + 1)`. -/
@[simp]
theorem iteratedFiberProductIdDiffeomorph_symm_apply (hn : 1 ≤ n) (m : ℕ) (x : M) :
    letI := iteratedFiberProductChartedSpace hn
      (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) m
    (iteratedFiberProductIdDiffeomorph (IM := IM) hn m).symm x =
      IteratedFiberProduct.const (m + 1) x := (rfl)

end Manifold

end TauCeti
