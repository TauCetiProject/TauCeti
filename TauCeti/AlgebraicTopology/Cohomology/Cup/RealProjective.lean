/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Cohomology
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.AlgebraicTopology.Cohomology.Kronecker
import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
import TauCeti.Geometry.Convex.ConvexSpace.Defs
import TauCeti.Geometry.Convex.ConvexSpace.LocallyPathConnectedSpaceStdSimplex

/-!
# The mod-two cup square on the real projective plane

The first mod-two cohomology `H¹(ℝP²; 𝔽₂)` is a line, and the square `w ⌣ w` of its nonzero class
`w` is nonzero (`TauCeti.RealProjectiveSpace.singularCup_self_ne_zero`): it is the nonzero class
of `H²(ℝP²; 𝔽₂)`. This is the first relation of the cohomology ring
`H*(ℝP²; 𝔽₂) = 𝔽₂[w] / (w³)`, and the reason why the cup length of `ℝP²` over `𝔽₂` is `2` while
over `ℚ` it is `0`: in characteristic two the square of a class of odd degree need not vanish.

The proof evaluates an explicit cocycle on an explicit cycle.

* **The cocycle.** Choose for every point of `ℝP²` one of its two unit-vector representatives,
  and call a unit vector `v` on the first sheet when it is the chosen one and on the second sheet
  otherwise, so that `v` and `-v` always lie on different sheets. A singular `1`-simplex `γ` of
  `ℝP²` lifts to the sphere, since the topological simplex is simply connected, and its value
  `w(γ) ∈ 𝔽₂` is the sum of the sheets of the two endpoints of a lift. Two lifts are equal or
  antipodal (`TauCeti.RealProjectiveSpace.eq_or_eq_neg_of_mk_comp_eq`), so this does not depend on
  the lift. Lifting a `2`-simplex, the values of `w` on its three edges add up to twice the sum of
  the sheets of its three vertices, so `w` is a cocycle.
* **The cycle.** The two triangles
  `σ±(t₀, t₁, t₂) = (±(t₁ - t₂), ±2 √(t₁ t₂), √(1 - (t₁ + t₂)²))`
  in the upper hemisphere of `S²` share the north pole as their vertex `0` and the two meridians
  through `(1, 0, 0)` and `(-1, 0, 0)` as edges, and their opposite edges are the two halves of the
  equator, which are antipodal. So in `ℝP²` the boundary of `σ₊ + σ₋` is twice the image of the
  half equator, a mod-two cycle.
* **The evaluation.** On a `2`-simplex, `w ⌣ w` is `w` of the front edge `[0, 1]` times `w` of
  the back edge `[1, 2]`. The back edges of `σ±` are halves of the equator, joining antipodal
  points, so `w` is `1` on both of them, and the front edges are the two meridians, whose values of
  `w` differ by one since their endpoints `(±1, 0, 0)` are antipodal. Hence `w ⌣ w` takes the value
  `1` on the cycle, and its class is not zero.

## Main results

* `TauCeti.RealProjectiveSpace.singularCup_self_ne_zero`: the cup square of every nonzero class of
  `H¹(ℝP²; 𝔽₂)` is nonzero.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Theorem 3.12, the cohomology rings of real projective spaces; the proof here is a
  direct evaluation on singular chains instead.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Metric Module Convexity Simplicial

namespace TauCeti.RealProjectiveSpace

/-! ### The cocycle of the double cover -/

section Cocycle

variable {n : ℕ}

/-- The sheet of a unit vector, `0` if it is the chosen representative of its line and `1` if it
is the other one. -/
private def sheet (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : ZMod 2 :=
  open Classical in if Function.surjInv (mk_surjective n) (mk n v) = v then 0 else 1

/-- Antipodal unit vectors lie on different sheets. -/
private theorem sheet_neg (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sheet (-v) = sheet v + 1 := by
  have hs := Function.surjInv_eq (mk_surjective n) (mk n v)
  rw [mk_eq_mk_iff] at hs
  have hv : -v ≠ v := (ne_neg_of_mem_unit_sphere ℝ v).symm
  simp only [sheet, mk_neg]
  rcases hs with h | h <;> simp only [h, hv, hv.symm, ↓reduceIte] <;> decide

/-- A map from a simply connected, locally path-connected space to `ℝPⁿ` lifts to the sphere. -/
private theorem exists_lift {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A] (f : C(A, RealProjectiveSpace n)) :
    ∃ F : C(A, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1), mk n ∘ F = f := by
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  obtain ⟨e, he⟩ := mk_surjective n (f a)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := (isCoveringMap_mk n).existsUnique_continuousMap_lifts f a e he
  exact ⟨F, hF⟩

/-- The sum of the sheets of two points of a lift does not depend on the lift. -/
private theorem sheet_add_sheet_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {F G : A → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1} (hF : Continuous F)
    (hG : Continuous G) (h : mk n ∘ F = mk n ∘ G) (a b : A) :
    sheet (G a) + sheet (G b) = sheet (F a) + sheet (F b) := by
  rcases eq_or_eq_neg_of_mk_comp_eq hF hG h with rfl | rfl
  · rfl
  · simp only [Pi.neg_apply, sheet_neg]
    rw [add_add_add_comm, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]

/-- The value of the cocycle on a singular `1`-simplex: the sum of the sheets of the endpoints of
a lift to the sphere. -/
private def cocycleValue (γ : (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))) _⦋1⦌) :
    ZMod 2 :=
  sheet ((exists_lift ((TopCat.of (RealProjectiveSpace n)).toSSetObjEquiv _ γ)).choose
      (.single 0)) +
    sheet ((exists_lift ((TopCat.of (RealProjectiveSpace n)).toSSetObjEquiv _ γ)).choose
      (.single 1))

/-- The value of the cocycle on an edge `g` of a singular simplex `σ` is the sum of the sheets of
the endpoints of the edge under any lift `Γ` of `σ`. -/
private theorem cocycleValue_map {m : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))) _⦋m⦌)
    (Γ : C(StdSimplex ℝ (Fin (m + 1)), sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hΓ : mk n ∘ Γ = (TopCat.of (RealProjectiveSpace n)).toSSetObjEquiv _ σ) (g : ⦋1⦌ ⟶ ⦋m⦌) :
    cocycleValue ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))).map g.op σ) =
      sheet (Γ (.single (g 0))) + sheet (Γ (.single (g 1))) := by
  obtain ⟨F, hF⟩ := exists_lift ((TopCat.of (RealProjectiveSpace n)).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))).map g.op σ))
  -- `Γ` restricted to the edge is a lift of the edge.
  have key := sheet_add_sheet_eq (G := fun z ↦ Γ (StdSimplex.map g z)) F.continuous
    (Γ.continuous.comp (StdSimplex.continuous_map ℝ _)) ?_ (.single 0) (.single 1)
  · simp only [StdSimplex.map_single] at key
    rw [key, cocycleValue]
    exact (sheet_add_sheet_eq (ContinuousMap.continuous _) F.continuous
      ((exists_lift _).choose_spec.trans hF.symm) _ _).symm
  funext z
  have := congrFun hF z
  simp only [Function.comp_apply] at this ⊢
  rw [this, TopCat.toSSetObjEquiv_naturality_apply]
  exact (congrFun hΓ _).symm

/-- The cocycle as a singular cochain with values in `𝔽₂`. -/
private def cochain : ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))).chainComplex
    (𝟙_ (ModuleCat.{0} (ZMod 2)))).X 1 ⟶ 𝟙_ (ModuleCat.{0} (ZMod 2)) :=
  Sigma.desc fun γ ↦ cocycleValue γ • 𝟙 _

private theorem ιChainComplex_cochain
    (γ : (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))) _⦋1⦌) :
    (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))).ιChainComplex γ ≫ cochain =
      cocycleValue γ • 𝟙 _ :=
  Sigma.ι_comp_desc _ _

/-- The cochain is a cocycle: on a `2`-simplex its values on the three edges add up to twice the
sum of the sheets of the vertices of a lift. -/
private theorem d_cochain :
    ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))).chainComplex
      (𝟙_ (ModuleCat.{0} (ZMod 2)))).d 2 1 ≫ cochain = 0 := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  obtain ⟨Γ, hΓ⟩ := exists_lift ((TopCat.of (RealProjectiveSpace n)).toSSetObjEquiv _ σ)
  simp only [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
    SimplicialObject.δ, ιChainComplex_cochain, cocycleValue_map σ Γ hΓ, comp_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h₀ : (Fin.succAbove 0 0 : Fin 3) = 1 := rfl
  have h₁ : (Fin.succAbove 0 1 : Fin 3) = 2 := rfl
  have h₂ : (Fin.succAbove 1 0 : Fin 3) = 0 := rfl
  have h₃ : (Fin.succAbove 1 1 : Fin 3) = 2 := rfl
  have h₄ : (Fin.succAbove 2 0 : Fin 3) = 0 := rfl
  have h₅ : (Fin.succAbove 2 1 : Fin 3) = 1 := rfl
  simp only [SimplexCategory.δ_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h₀, h₁, h₂, h₃,
    h₄, h₅, ← Int.cast_smul_eq_zsmul (ZMod 2), smul_smul, ← add_smul, add_zero]
  convert zero_smul (ZMod 2) (𝟙 (𝟙_ (ModuleCat.{0} (ZMod 2))))
  generalize sheet (Γ (.single 0)) = a
  generalize sheet (Γ (.single 1)) = b
  generalize sheet (Γ (.single 2)) = c
  revert a b c
  decide

/-- The cocycle of the double cover `Sⁿ → ℝPⁿ`, with values in `𝔽₂`. -/
private def cocycle (n : ℕ) :
    ((TopCat.of (RealProjectiveSpace n)).singularCochainComplex (𝟙_ (ModuleCat.{0} (ZMod 2)))
      (ZMod 2) (𝟙_ (ModuleCat.{0} (ZMod 2)))).cycles 1 :=
  HomologicalComplex.moduleCatCyclesMk _ cochain 2 (by simp)
    ((TauCeti.ChainComplex.linearYonedaObj_d_apply 1 2 _).trans d_cochain)

private theorem iCycles_cocycle (n : ℕ) :
    ((TopCat.of (RealProjectiveSpace n)).singularCochainComplex (𝟙_ (ModuleCat.{0} (ZMod 2)))
      (ZMod 2) (𝟙_ (ModuleCat.{0} (ZMod 2)))).iCycles 1 (cocycle n) = cochain :=
  HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _
    ((TauCeti.ChainComplex.linearYonedaObj_d_apply 1 2 _).trans d_cochain)

/-- On a `2`-simplex, the cup square of the cocycle is the product of its values on the front and
back edges. -/
private theorem ιChainComplex_cupCochain_cochain
    (σ : (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))) _⦋2⦌) :
    (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))).ιChainComplex σ ≫
      TauCeti.ChainComplex.cupCochain (ZMod 2)
        ((TopCat.of (RealProjectiveSpace n)).alexanderWhitneyDiagonal
          (λ_ (𝟙_ (ModuleCat.{0} (ZMod 2)))).inv)
        (λ_ (𝟙_ (ModuleCat.{0} (ZMod 2)))).hom 1 1 2 rfl cochain cochain =
    (cocycleValue ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))).map
        (SimplexCategory.subinterval 0 1 (by omega)).op σ) *
      cocycleValue ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace n))).map
        (SimplexCategory.subinterval 1 1 (by omega)).op σ)) • 𝟙 (𝟙_ (ModuleCat.{0} (ZMod 2))) := by
  rw [TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal, ιChainComplex_cochain,
    ιChainComplex_cochain]
  simp only [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, smul_smul,
    MonoidalCategory.whiskerLeft_id, Iso.inv_hom_id, MonoidalCategory.id_whiskerRight,
    Category.id_comp, mul_comm]

end Cocycle

/-! ### Two hemisphere triangles -/

section Cycle

/-- The point `(s (t₁ - t₂), 2 s √(t₁ t₂), √(1 - (t₁ + t₂)²))` of the upper hemisphere of `S²`,
for `t` in the standard `2`-simplex and a sign `s = ±1`. -/
private def hemisphereVec (s : ℝ) (t : StdSimplex ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  !₂[s * (t.weights 1 - t.weights 2), s * (2 * √(t.weights 1 * t.weights 2)),
    √(1 - (t.weights 1 + t.weights 2) ^ 2)]

private theorem hemisphereVec_mem {s : ℝ} (hs : s ^ 2 = 1) (t : StdSimplex ℝ (Fin 3)) :
    hemisphereVec s t ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have h1 := t.weights_nonneg 1
  have h2 := t.weights_nonneg 2
  have hle := t.weights_one_add_weights_two_le_one
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three]
  simp only [hemisphereVec, Real.norm_eq_abs, sq_abs, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_pow,
    Real.sq_sqrt (mul_nonneg h1 h2),
    Real.sq_sqrt (show 0 ≤ 1 - (t.weights 1 + t.weights 2) ^ 2 by nlinarith)]
  linear_combination ((t.weights 1 - t.weights 2) ^ 2 + 4 * (t.weights 1 * t.weights 2)) * hs

/-- The hemisphere triangle `σ_s` as a map from the standard `2`-simplex to the sphere. -/
private def hemisphereSimplex (s : ℝ) (hs : s ^ 2 = 1) :
    C(StdSimplex ℝ (Fin 3), sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨fun t ↦ ⟨hemisphereVec s t, hemisphereVec_mem hs t⟩, by
    refine Continuous.subtype_mk ?_ _
    unfold hemisphereVec
    fun_prop⟩

/-- The hemisphere triangle `σ_s` as a singular `2`-simplex of `ℝP²`. -/
private def hemisphereSingular (s : ℝ) (hs : s ^ 2 = 1) :
    (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))) _⦋2⦌ :=
  ((TopCat.of (RealProjectiveSpace 2)).toSSetObjEquiv _).symm ⟨mk 2 ∘ hemisphereSimplex s hs,
    (continuous_mk 2).comp (hemisphereSimplex s hs).continuous⟩

private theorem mk_comp_hemisphereSimplex (s : ℝ) (hs : s ^ 2 = 1) :
    mk 2 ∘ hemisphereSimplex s hs =
      (TopCat.of (RealProjectiveSpace 2)).toSSetObjEquiv _ (hemisphereSingular s hs) := by
  rw [hemisphereSingular, Equiv.apply_symm_apply]
  rfl

private theorem δ_hemisphereSingular_eq {s s' : ℝ} (hs : s ^ 2 = 1) (hs' : s' ^ 2 = 1)
    (i j : Fin 3)
    (h : ∀ z : StdSimplex ℝ (Fin 2),
      mk 2 (hemisphereSimplex s hs (StdSimplex.map i.succAbove z)) =
        mk 2 (hemisphereSimplex s' hs' (StdSimplex.map j.succAbove z))) :
    (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).δ i (hemisphereSingular s hs) =
      (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).δ j (hemisphereSingular s' hs') := by
  apply ((TopCat.of (RealProjectiveSpace 2)).toSSetObjEquiv _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply,
    ← mk_comp_hemisphereSimplex, ← mk_comp_hemisphereSimplex]
  exact h z

/-- The edges `[1, 2]` of the two triangles are antipodal halves of the equator, so they have the
same image in `ℝP²`. -/
private theorem δ_zero_hemisphereSingular :
    (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).δ 0
        (hemisphereSingular 1 (one_pow 2)) =
      (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).δ 0
        (hemisphereSingular (-1) (by norm_num)) := by
  refine δ_hemisphereSingular_eq _ _ 0 0 fun z ↦ ?_
  have hp1 := StdSimplex.weights_map_succAbove_of_eq (R := ℝ) (j := 0) (k := 1) (i := 0) rfl z
  have hp2 := StdSimplex.weights_map_succAbove_of_eq (R := ℝ) (j := 0) (k := 2) (i := 1) rfl z
  have hz := z.total_fin_two
  simp only [Fin.succAbove_zero] at hp1 hp2
  rw [← mk_neg]
  congr 1
  apply Subtype.ext
  ext k
  fin_cases k <;> simp [hemisphereSimplex, hemisphereVec, hp1, hp2, hz, -StdSimplex.weights_map]

/-- The edge `[0, 2]` of `σ₊` and the edge `[0, 1]` of `σ₋` are the same meridian. -/
private theorem δ_one_hemisphereSingular :
    (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).δ 1
        (hemisphereSingular 1 (one_pow 2)) =
      (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).δ 2
        (hemisphereSingular (-1) (by norm_num)) := by
  refine δ_hemisphereSingular_eq _ _ 1 2 fun z ↦ ?_
  have hp1 := StdSimplex.weights_map_succAbove_self (R := ℝ) (1 : Fin 3) z
  have hp2 := StdSimplex.weights_map_succAbove_of_eq (R := ℝ) (j := 1) (k := 2) (i := 1) rfl z
  have hq1 := StdSimplex.weights_map_succAbove_of_eq (R := ℝ) (j := 2) (k := 1) (i := 1) rfl z
  have hq2 := StdSimplex.weights_map_succAbove_self (R := ℝ) (2 : Fin 3) z
  congr 1
  apply Subtype.ext
  ext k
  fin_cases k <;> simp [hemisphereSimplex, hemisphereVec, hp1, hp2, hq1, hq2,
    -StdSimplex.weights_map]

/-- The edge `[0, 1]` of `σ₊` and the edge `[0, 2]` of `σ₋` are the same meridian. -/
private theorem δ_two_hemisphereSingular :
    (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).δ 2
        (hemisphereSingular 1 (one_pow 2)) =
      (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).δ 1
        (hemisphereSingular (-1) (by norm_num)) :=
  (δ_hemisphereSingular_eq _ _ 1 2 fun z ↦ by
    have hp1 := StdSimplex.weights_map_succAbove_self (R := ℝ) (1 : Fin 3) z
    have hp2 := StdSimplex.weights_map_succAbove_of_eq (R := ℝ) (j := 1) (k := 2) (i := 1) rfl z
    have hq1 := StdSimplex.weights_map_succAbove_of_eq (R := ℝ) (j := 2) (k := 1) (i := 1) rfl z
    have hq2 := StdSimplex.weights_map_succAbove_self (R := ℝ) (2 : Fin 3) z
    congr 1
    apply Subtype.ext
    ext k
    fin_cases k <;> simp [hemisphereSimplex, hemisphereVec, hp1, hp2, hq1, hq2,
      -StdSimplex.weights_map]).symm

/-- The sum `σ₊ + σ₋` of the two hemisphere triangles, a singular `2`-chain of `ℝP²` with
coefficients in `𝔽₂`. -/
private def hemisphereChain : 𝟙_ (ModuleCat.{0} (ZMod 2)) ⟶
    ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).chainComplex
      (𝟙_ (ModuleCat.{0} (ZMod 2)))).X 2 :=
  (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).ιChainComplex
      (hemisphereSingular 1 (one_pow 2)) +
    (TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).ιChainComplex
      (hemisphereSingular (-1) (by norm_num))

/-- The sum of the two hemisphere triangles is a mod-two cycle: its boundary is twice the image of
the half equator. -/
private theorem hemisphereChain_d :
    hemisphereChain ≫ ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).chainComplex
      (𝟙_ (ModuleCat.{0} (ZMod 2)))).d 2 1 = 0 := by
  simp only [hemisphereChain, Preadditive.add_comp, SSet.ιChainComplex_d, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [δ_zero_hemisphereSingular, δ_one_hemisphereSingular, δ_two_hemisphereSingular]
  simp only [pow_zero, pow_one, one_smul, neg_one_sq, neg_smul, add_zero]
  abel_nf
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_smul]

private theorem hemisphereSimplex_single_zero {s : ℝ} (hs : s ^ 2 = 1) :
    hemisphereSimplex s hs (.single 0) = hemisphereSimplex 1 (one_pow 2) (.single 0) := by
  apply Subtype.ext
  ext k
  fin_cases k <;> simp [hemisphereSimplex, hemisphereVec]

private theorem hemisphereSimplex_single_two {s : ℝ} (hs : s ^ 2 = 1) :
    hemisphereSimplex s hs (.single 2) = -hemisphereSimplex s hs (.single 1) := by
  apply Subtype.ext
  ext k
  fin_cases k <;> simp [hemisphereSimplex, hemisphereVec]

private theorem hemisphereSimplex_neg_one_single_one :
    hemisphereSimplex (-1) (by norm_num) (.single 1) =
      -hemisphereSimplex 1 (one_pow 2) (.single 1) := by
  apply Subtype.ext
  ext k
  fin_cases k <;> simp [hemisphereSimplex, hemisphereVec]

/-- The cup square of the cocycle takes the value `1` on the sum of the two hemisphere triangles.
-/
private theorem hemisphereChain_cupCochain :
    hemisphereChain ≫ TauCeti.ChainComplex.cupCochain (ZMod 2)
      ((TopCat.of (RealProjectiveSpace 2)).alexanderWhitneyDiagonal
        (λ_ (𝟙_ (ModuleCat.{0} (ZMod 2)))).inv)
        (λ_ (𝟙_ (ModuleCat.{0} (ZMod 2)))).hom 1 1 2 rfl cochain cochain =
      𝟙 (𝟙_ (ModuleCat.{0} (ZMod 2))) := by
  rw [hemisphereChain, Preadditive.add_comp, ιChainComplex_cupCochain_cochain,
    ιChainComplex_cupCochain_cochain, ← add_smul]
  have h₀ : ∀ h, (SimplexCategory.subinterval (n := 2) 0 1 h : Fin 2 → Fin 3) 0 = 0 :=
    fun _ ↦ rfl
  have h₁ : ∀ h, (SimplexCategory.subinterval (n := 2) 0 1 h : Fin 2 → Fin 3) 1 = 1 :=
    fun _ ↦ rfl
  have h₂ : ∀ h, (SimplexCategory.subinterval (n := 2) 1 1 h : Fin 2 → Fin 3) 0 = 1 :=
    fun _ ↦ rfl
  have h₃ : ∀ h, (SimplexCategory.subinterval (n := 2) 1 1 h : Fin 2 → Fin 3) 1 = 2 :=
    fun _ ↦ rfl
  simp only [cocycleValue_map _ _ (mk_comp_hemisphereSimplex _ _), h₀, h₁, h₂, h₃]
  rw [hemisphereSimplex_single_two (s := 1), hemisphereSimplex_single_two (s := -1),
    hemisphereSimplex_single_zero (s := -1), hemisphereSimplex_neg_one_single_one, neg_neg]
  simp only [sheet_neg]
  convert one_smul (ZMod 2) (𝟙 (𝟙_ (ModuleCat.{0} (ZMod 2))))
  generalize sheet (hemisphereSimplex 1 (one_pow 2) (.single 0)) = a
  generalize sheet (hemisphereSimplex 1 (one_pow 2) (.single 1)) = b
  revert a b
  decide

end Cycle

/-! ### The cup square -/

/-- The cup square of the class of the cocycle of the double cover is nonzero, since it takes the
value `1` on the cycle of the two hemisphere triangles. -/
private theorem singularCup_homologyπ_cocycle_ne_zero :
    (TopCat.of (RealProjectiveSpace 2)).singularCup (ZMod 2) (λ_ _).inv (λ_ _).hom 1 1 2 rfl
      (((TopCat.of (RealProjectiveSpace 2)).singularCochainComplex _ (ZMod 2) _).homologyπ 1
        (cocycle 2))
      (((TopCat.of (RealProjectiveSpace 2)).singularCochainComplex _ (ZMod 2) _).homologyπ 1
        (cocycle 2)) ≠ 0 := by
  intro h
  rw [TopCat.singularCup_homologyπ] at h
  have key : ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).chainComplex _).liftCycles
      hemisphereChain 1 (by simp) hemisphereChain_d ≫
        ((TopCat.toSSet.obj (TopCat.of (RealProjectiveSpace 2))).chainComplex _).homologyπ 2 ≫
          (TopCat.of (RealProjectiveSpace 2)).singularKronecker (ZMod 2) 2
            (((TopCat.of (RealProjectiveSpace 2)).singularCochainComplex _ (ZMod 2) _).homologyπ 2
              (TauCeti.ChainComplex.cupCycles (ZMod 2)
                ((TopCat.of (RealProjectiveSpace 2)).alexanderWhitneyDiagonal (λ_ _).inv)
                (λ_ _).hom 1 1 2 rfl (cocycle 2) (cocycle 2))) =
        𝟙 (𝟙_ (ModuleCat.{0} (ZMod 2))) := by
    simp only [TopCat.singularKronecker_homologyπ, HomologicalComplex.liftCycles_i_assoc,
      TauCeti.ChainComplex.iCycles_cupCycles]
    rw [iCycles_cocycle, hemisphereChain_cupCochain]
  rw [h, map_zero] at key
  have h0 : 𝟙 (𝟙_ (ModuleCat.{0} (ZMod 2))) = 0 :=
    key.symm.trans ((congrArg _ Limits.comp_zero).trans Limits.comp_zero)
  have h1 := congrArg (fun f ↦ f.hom (1 : ZMod 2)) h0
  simp only [ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h1
  exact (by decide : (1 : ZMod 2) ≠ 0) h1

/-- **The square of the nonzero class of `H¹(ℝP²; 𝔽₂)` is nonzero.** The first mod-two cohomology
of the real projective plane is a line, and the cup square `a ⌣ a ∈ H²(ℝP²; 𝔽₂)` of each of its
nonzero classes `a` is nonzero. -/
theorem singularCup_self_ne_zero
    {a : (TopCat.of (RealProjectiveSpace 2)).singularCohomology (𝟙_ (ModuleCat.{0} (ZMod 2)))
      (ZMod 2) (𝟙_ (ModuleCat.{0} (ZMod 2))) 1} (ha : a ≠ 0) :
    (TopCat.of (RealProjectiveSpace 2)).singularCup (ZMod 2) (λ_ _).inv (λ_ _).hom 1 1 2 rfl a a ≠
      0 := by
  have hc : ((TopCat.of (RealProjectiveSpace 2)).singularCochainComplex _ (ZMod 2) _).homologyπ 1
      (cocycle 2) ≠ 0 := fun hc ↦ singularCup_homologyπ_cocycle_ne_zero (by
    rw [hc, map_zero])
  -- `H¹(ℝP²; 𝔽₂)` is a line, so its nonzero classes are multiples `r • c` with `r ≠ 0`, that is
  -- with `r = 1`.
  have hrank : finrank (ZMod 2) ((TopCat.of (RealProjectiveSpace 2)).singularCohomology
      (𝟙_ (ModuleCat.{0} (ZMod 2))) (ZMod 2) (𝟙_ (ModuleCat.{0} (ZMod 2))) 1) = 1 :=
    finrank_singularCohomology_of_two_eq_zero (N := 2) rfl 1
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_ne_zero' (K := ZMod 2) _ hc).1 hrank a
  obtain rfl : r = 1 :=
    (by decide : ∀ r : ZMod 2, r ≠ 0 → r = 1) r fun h ↦ ha (by rw [← hr, h, zero_smul])
  rw [← hr, one_smul]
  exact singularCup_homologyπ_cocycle_ne_zero

end TauCeti.RealProjectiveSpace
