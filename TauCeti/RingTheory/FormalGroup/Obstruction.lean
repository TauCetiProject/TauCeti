/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
-- Proof-only: the order filtration on points, substitution into points, the symmetric 2-cocycle
-- lemma, lowest-degree parts of substitutions, two-variable substitution identities, and the
-- permutations of `Fin 2`.
import TauCeti.Data.Fin.Basic
import TauCeti.RingTheory.FormalGroup.Point.Order
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification
import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The obstruction to extending a homomorphism of formal group laws

Let `F` and `G` be commutative formal group laws over a commutative ring `R`, and let `f` be a
power series without constant term which is a homomorphism from `F` to `G` up to degree `n`: the
**homomorphism defect** `f(F(X, Y)) - G(f(X), f(Y))` (`FormalGroup.homDefect`) vanishes below
degree `n`. Its degree-`n` part is the obstruction to improving `f` to a homomorphism up to degree
`n + 1`. This file shows that the obstruction is a multiple `c C_n` of the Lazard cocycle
`C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`, and that when `n = pᵏ` and `p = 0` in `R`, the scalar `c` is the
coefficient of `Xⁿ` in `[p]_G(f(X)) - f([p]_F(X))`. Since `d_n` is a unit in `R` unless `n` is a
power of `p`, only the degrees `pᵏ` carry a genuine obstruction, and it is read off the
`p`-series: this is the degree-by-degree mechanism behind Lazard's classification of formal group
laws over separably closed fields by their height.

The argument takes place in the group `G.Point σ` of power-series points of `G`. The defect
`δ(x, y) = f(x + y) - f(x) - f(y)`, computed there, satisfies the cocycle identity, the symmetry
and the telescoping `f(p x) - p f(x) = ∑_{j < p} δ(j x, x)` exactly, as identities in an abelian
group. The points vanishing to order `N ≥ 1` form a subgroup on which the degree-`N` part is
additive (`FormalGroup.homogeneousComponent_val_sub`, from `FormalGroup.le_order_subst_sub_sub`:
`G(w, v) = w + v` up to degree `N + 1` when `w` vanishes to order `N`), and the defect at any pair
of points is obtained from the defect at the coordinate points by substitution
(`FormalGroup.substPointHom`), so these identities pass to the degree-`n` part of the defect,
which is then a symmetric additive 2-cocycle, hence a multiple of `C_n` by the symmetric 2-cocycle
lemma `TauCeti.exists_eq_smul_lazardCocycle`; its value in degree `pᵏ` comes from the identity
`∑_{j < p} C_{pᵏ}(j, 1) = -1` in characteristic `p`.

The homomorphism defect itself and its basic API are in
`TauCeti.RingTheory.FormalGroup.Hom`.

## Main results

* `FormalGroup.exists_homogeneousComponent_eq_smul_lazardCocycle`: the leading term of a symmetric
  series satisfying the 2-cocycle identity along a formal group law up to higher-order terms is a
  multiple of the Lazard cocycle.
* `FormalGroup.exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle`: the leading term of
  the homomorphism defect is a multiple `c C_n` of the Lazard cocycle.
* `FormalGroup.homogeneousComponent_homDefect_eq_smul_lazardCocycle`: in degree `pᵏ` and
  characteristic `p`, the multiple is the coefficient of `X^(pᵏ)` in `[p]_G ∘ f - f ∘ [p]_F`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* A. Fröhlich, *Formal Groups*, Lecture Notes in Mathematics 74, Springer (1968), Chapter III.
* J. Lurie, *Chromatic Homotopy Theory* (Harvard lecture notes, 2010), Lecture 13.
-/

public section

open MvPowerSeries

namespace FormalGroup
variable {R : Type*} [CommRing R]

section Cocycle

/-- **Leading terms of symmetric 2-cocycles.** Let `F` be a formal group law and let
`Φ(X, Y)` be a symmetric series vanishing below degree `n ≠ 0` that satisfies the 2-cocycle
identity `Φ(X, Y) + Φ(F(X, Y), Z) = Φ(X, F(Y, Z)) + Φ(Y, Z)` up to terms of degree above `n`.
Then the degree-`n` part of `Φ` is a multiple of the Lazard cocycle `C_n`. -/
theorem exists_homogeneousComponent_eq_smul_lazardCocycle (F : FormalGroup R) {n : ℕ}
    (hn : n ≠ 0) {Φ : MvPowerSeries (Fin 2) R} (hΦ : n ≤ Φ.order)
    (hsymm : Φ.subst ![X 1, X 0] = Φ)
    (hcocycle : ((n + 1 : ℕ) : ℕ∞) ≤ (Φ.subst ![X 0, X 1] +
      Φ.subst ![F.toPowerSeries.subst ![X 0, X 1], (X 2 : MvPowerSeries (Fin 3) R)] -
      Φ.subst ![X 0, F.toPowerSeries.subst ![X 1, X 2]] -
      Φ.subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2]).order) :
    ∃ c : R, homogeneousComponent n Φ = ↑(c • TauCeti.lazardCocycle n R) := by
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
  have hX₀ (i : Fin 3) := constantCoeff_X (R := R) i
  have hF₀ (i j : Fin 3) :
      constantCoeff (F.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j]) = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero (hasSubst_finTwo (hX i) (hX j))
      (fun s ↦ by fin_cases s <;> simp) F.toPowerSeries, F.zero_constantCoeff, map_zero]
  -- the leading polynomial is an additive 2-cocycle
  have hcoc : (homogeneousComponentPolynomial n Φ).IsAddCocycle₂ := by
    have h := homogeneousComponent_of_lt_order_eq_zero
      (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hcocycle)
    rw [map_sub, map_sub, map_add,
      homogeneousComponent_subst_eq_coe_aeval hΦ (hasSubst_finTwo (hX 0) (hX 1))
        (l := ![MvPolynomial.X 0, MvPolynomial.X 1]) (fun i ↦ by fin_cases i <;> simp)
        (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X]),
      homogeneousComponent_subst_eq_coe_aeval hΦ
        (hasSubst_finTwo (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2))
        (l := ![MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 2])
        (fun i ↦ by fin_cases i <;> simp [hF₀])
        (fun i ↦ by
          fin_cases i <;>
            simp [homogeneousComponent_one_subst_pair F.zero_constantCoeff F.lin_coeff_X
              F.lin_coeff_Y (hX₀ 0) (hX₀ 1), homogeneousComponent_one_X]),
      homogeneousComponent_subst_eq_coe_aeval hΦ
        (hasSubst_finTwo (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2)))
        (l := ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.X 2])
        (fun i ↦ by fin_cases i <;> simp [hF₀])
        (fun i ↦ by
          fin_cases i <;>
            simp [homogeneousComponent_one_subst_pair F.zero_constantCoeff F.lin_coeff_X
              F.lin_coeff_Y (hX₀ 1) (hX₀ 2), homogeneousComponent_one_X]),
      homogeneousComponent_subst_eq_coe_aeval hΦ (hasSubst_finTwo (hX 1) (hX 2))
        (l := ![MvPolynomial.X 1, MvPolynomial.X 2]) (fun i ↦ by fin_cases i <;> simp)
        (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X])] at h
    rw [MvPolynomial.isAddCocycle₂_iff]
    refine MvPolynomial.coe_inj.mp ?_
    rw [MvPolynomial.coe_add, MvPolynomial.coe_add]
    linear_combination h
  -- the leading polynomial is symmetric
  have hsym : (homogeneousComponentPolynomial n Φ).IsSymmetric := by
    have hX2 (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
    have h : MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 0]
        (homogeneousComponentPolynomial n Φ) = homogeneousComponentPolynomial n Φ := by
      refine MvPolynomial.coe_inj.mp ?_
      rw [← homogeneousComponent_subst_eq_coe_aeval hΦ (hasSubst_finTwo (hX2 1) (hX2 0))
        (fun i ↦ by fin_cases i <;> simp)
        (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X]), hsymm,
        coe_homogeneousComponentPolynomial]
    intro e
    rcases Equiv.Perm.eq_one_or_swap_fin_two e with rfl | rfl
    · simp
    · have hswap : (MvPolynomial.X ∘ Equiv.swap (0 : Fin 2) 1 : Fin 2 → MvPolynomial (Fin 2) R) =
          ![MvPolynomial.X 1, MvPolynomial.X 0] := by
        funext i
        fin_cases i <;> simp
      rw [MvPolynomial.rename_eq_aeval, hswap]
      exact h
  obtain ⟨c, hc⟩ := TauCeti.exists_eq_smul_lazardCocycle hn
    (isHomogeneous_homogeneousComponentPolynomial _ _) hsym hcoc
  exact ⟨c, by rw [← coe_homogeneousComponentPolynomial]; exact congrArg _ hc⟩

end Cocycle

section Defect

variable {F G : FormalGroup R} {f : PowerSeries R} {σ : Type*}

/-- The point `f(x)` of `G`, for a series `f` without constant term and a point `x` of `F`. -/
private noncomputable def evalPoint (G : FormalGroup R) (hf : PowerSeries.constantCoeff f = 0)
    (x : F.Point σ) : G.Point σ :=
  ⟨PowerSeries.subst x.val f, by
    simpa only [PowerSeries.coe_substAlgHom] using
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf).comp x.prop⟩

private theorem val_evalPoint (G : FormalGroup R) (hf : PowerSeries.constantCoeff f = 0)
    (x : F.Point σ) : (evalPoint G hf x).val = PowerSeries.subst x.val f := (rfl)

/-- The defect `f(x + y) - f(x) - f(y)` in the points of `G`. -/
private noncomputable def defectPoint (G : FormalGroup R) (hf : PowerSeries.constantCoeff f = 0)
    (x y : F.Point σ) : G.Point σ :=
  evalPoint G hf (x + y) - evalPoint G hf x - evalPoint G hf y

/-- The coordinate point `X i` of `F`. -/
private noncomputable def coordPoint (F : FormalGroup R) (i : σ) : F.Point σ :=
  ⟨X i, PowerSeries.HasSubst.X i⟩

/-- The defect at the coordinate points `X` and `Y` of `F`. -/
private noncomputable def coordDefect (F G : FormalGroup R)
    (hf : PowerSeries.constantCoeff f = 0) : G.Point (Fin 2) :=
  defectPoint G hf (coordPoint F 0) (coordPoint F 1)

private theorem constantCoeff_evalPoint (hf : PowerSeries.constantCoeff f = 0) {x : F.Point σ}
    (hx : constantCoeff x.val = 0) : constantCoeff (evalPoint G hf x).val = 0 := by
  rw [val_evalPoint, PowerSeries.subst,
    constantCoeff_subst_of_constantCoeff_zero x.prop.const (fun _ ↦ hx)]
  exact (congrArg _ hf).trans (map_zero _)

private theorem substPointHom_evalPoint (hf : PowerSeries.constantCoeff f = 0) {τ : Type*}
    {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (x : F.Point σ) :
    G.substPointHom ha (evalPoint G hf x) = evalPoint G hf (F.substPointHom ha x) :=
  Subtype.ext <| by
    rw [val_substPointHom, val_evalPoint, val_evalPoint, val_substPointHom]
    exact subst_powerSeriesSubst ha x.prop f

/-- The defect at any pair of points is obtained from the defect at the coordinate points by
substitution. -/
private theorem defectPoint_eq_substPointHom (hf : PowerSeries.constantCoeff f = 0)
    (x y : F.Point σ) :
    defectPoint G hf x y = G.substPointHom (hasSubst_finTwo x.prop y.prop)
      (coordDefect F G hf) := by
  have h0 : F.substPointHom (hasSubst_finTwo x.prop y.prop) (coordPoint F 0) = x :=
    Subtype.ext ((val_substPointHom _ _ _).trans (subst_X (hasSubst_finTwo x.prop y.prop) 0))
  have h1 : F.substPointHom (hasSubst_finTwo x.prop y.prop) (coordPoint F 1) = y :=
    Subtype.ext ((val_substPointHom _ _ _).trans (subst_X (hasSubst_finTwo x.prop y.prop) 1))
  simp only [coordDefect, defectPoint, map_sub, substPointHom_evalPoint, map_add, h0, h1]

/-- The defect is a 2-cocycle, by associativity of `F`. -/
private theorem defectPoint_add_defectPoint [G.IsComm] (hf : PowerSeries.constantCoeff f = 0)
    (x y z : F.Point σ) :
    defectPoint G hf x y + defectPoint G hf (x + y) z =
      defectPoint G hf y z + defectPoint G hf x (y + z) := by
  simp only [defectPoint, add_assoc]
  abel

/-- The defect is symmetric when `F` and `G` are commutative. -/
private theorem defectPoint_comm [F.IsComm] [G.IsComm] (hf : PowerSeries.constantCoeff f = 0)
    (x y : F.Point σ) : defectPoint G hf y x = defectPoint G hf x y := by
  simp only [defectPoint, add_comm y x]
  abel

/-- **The defect along multiples**: `f(m x) - m f(x)` telescopes to the sum of the defects
`f(j x + x) - f(j x) - f(x)` over `j < m`. -/
private theorem evalPoint_nsmul_sub_nsmul [G.IsComm] (hf : PowerSeries.constantCoeff f = 0)
    (x : F.Point σ) (m : ℕ) :
    evalPoint G hf (m • x) - m • evalPoint G hf x =
      ∑ j ∈ Finset.range m, defectPoint G hf (j • x) x := by
  induction m with
  | zero =>
    rw [zero_nsmul, zero_nsmul, Finset.sum_range_zero, sub_zero]
    exact Subtype.ext (PowerSeries.subst_zero_of_constantCoeff_zero hf)
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, defectPoint, succ_nsmul, succ_nsmul]
    abel

end Defect

section Obstruction

variable {F G : FormalGroup R} {f : PowerSeries R} {σ : Type*}

private theorem val_coordPoint (i : σ) : (coordPoint F i).val = X i := (rfl)

private theorem constantCoeff_coordPoint (i : σ) :
    constantCoeff (coordPoint F i).val = 0 :=
  constantCoeff_X i

private theorem coordDefect_eq (hf : PowerSeries.constantCoeff f = 0) :
    coordDefect F G hf = defectPoint G hf (coordPoint F 0) (coordPoint F 1) := (rfl)

/-- The homomorphism defect `f(X +_F Y) - (f(X) +_G f(Y))` is the ordinary difference of the
values at the coordinate points of the point `f(X +_F Y)` and the sum `f(X) +_G f(Y)` in `G`. -/
private theorem homDefect_eq_val_sub (hf : PowerSeries.constantCoeff f = 0) :
    F.homDefect G f = (evalPoint G hf (coordPoint F (0 : Fin 2) + coordPoint F 1)).val -
      (evalPoint G hf (coordPoint F (0 : Fin 2)) + evalPoint G hf (coordPoint F 1)).val := by
  simp only [homDefect_def, val_evalPoint, add_apply, val_coordPoint]
  congr 1
  · rw [finTwo_X_eq_X, subst_self, id]
  · congr 1
    funext i
    fin_cases i <;> simp [PowerSeries.toMvPowerSeries_eq_subst]

private theorem constantCoeff_evalPoint_add_evalPoint (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (evalPoint G hf (coordPoint F (0 : Fin 2)) +
      evalPoint G hf (coordPoint F 1)).val = 0 := by
  have h (i : Fin 2) := constantCoeff_evalPoint (G := G) hf (constantCoeff_coordPoint (F := F) i)
  exact G.constantCoeff_val_add (h 0) (h 1)

/-- If the defect at the coordinate points vanishes below degree `n`, so does the defect at any
pair of points without constant term. -/
private theorem le_order_defectPoint (hf : PowerSeries.constantCoeff f = 0) {n : ℕ}
    (hΨ : (n : ℕ∞) ≤ (coordDefect F G hf).val.order)
    {x y : F.Point σ} (hx : constantCoeff x.val = 0) (hy : constantCoeff y.val = 0) :
    (n : ℕ∞) ≤ (defectPoint G hf x y).val.order := by
  rw [defectPoint_eq_substPointHom, val_substPointHom]
  refine le_trans ?_ (le_order_subst (hasSubst_finTwo x.prop y.prop) _)
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (![x.val, y.val] i).order :=
    le_iInf fun i ↦ by
      fin_cases i <;> exact one_le_order_iff_constCoeff_eq_zero.mpr (by simpa)
  calc (n : ℕ∞) = 1 * n := (one_mul _).symm
    _ ≤ _ := mul_le_mul' h1 hΨ

/-- If the degree-`n` part of the defect at the coordinate points is `c C_n`, then the degree-`n`
part of the defect `f(j X + X) - f(j X) - f(X)` at multiples of the tautological point is
`c C_n(j X, X)`, since the linear part of `[j]_F(X)` is `j X`. -/
private theorem homogeneousComponent_defectPoint_nsmul (hf : PowerSeries.constantCoeff f = 0)
    {n : ℕ} (hΨ : (n : ℕ∞) ≤ (coordDefect F G hf).val.order) {c : R}
    (hc : homogeneousComponent n (coordDefect F G hf).val = ↑(c • TauCeti.lazardCocycle n R))
    (j : ℕ) :
    homogeneousComponent n
        (defectPoint G hf (j • F.tautologicalPoint) F.tautologicalPoint).val =
      MvPolynomial.coeToMvPowerSeries.ringHom (c • MvPolynomial.aeval
        ![(j : MvPolynomial Unit R) * MvPolynomial.X (), MvPolynomial.X ()]
        (TauCeti.lazardCocycle n R)) := by
  set x := F.tautologicalPoint
  have hx : constantCoeff x.val = 0 := by
    rw [val_tautologicalPoint]; exact PowerSeries.constantCoeff_X
  have hjx : (j • x).val = F.nsmulSeries j := by
    rw [← subst_nsmulSeries, val_tautologicalPoint, PowerSeries.X_subst]
  have hjx₀ : constantCoeff (j • x).val = 0 := by
    rw [hjx]; exact F.constantCoeff_nsmulSeries j
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, ← _root_.map_smul,
    defectPoint_eq_substPointHom, val_substPointHom, homogeneousComponent_subst_of_le_order
    hΨ (hasSubst_finTwo (j • x).prop x.prop)
    (fun i ↦ by fin_cases i; exacts [hjx₀, hx]), hc, ← subst_coe_pair_eq_coe_aeval]
  congr 1
  funext i
  fin_cases i
  · -- the linear part of `[j]_F` is `j X`
    have hj : ((j : MvPolynomial Unit R) : MvPowerSeries Unit R) = j :=
      map_natCast MvPolynomial.coeToMvPowerSeries.ringHom j
    simp [hjx, homogeneousComponent_one_eq_C_mul_X, ← PowerSeries.coeff_def, hj]
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, x,
      val_tautologicalPoint, MvPolynomial.coe_X]
    exact homogeneousComponent_one_X (R := R) ()

variable [G.IsComm]

private theorem defectPoint_coord_eq_sub (hf : PowerSeries.constantCoeff f = 0) :
    coordDefect F G hf =
      evalPoint G hf (coordPoint F (0 : Fin 2) + coordPoint F 1) -
        (evalPoint G hf (coordPoint F (0 : Fin 2)) + evalPoint G hf (coordPoint F 1)) := by
  rw [coordDefect, defectPoint, sub_sub]

/-- The defect at the coordinate points vanishes below degree `n` when the homomorphism defect
does, and their degree-`n` parts agree. -/
private theorem le_order_defectPoint_coord (hf : PowerSeries.constantCoeff f = 0) {n : ℕ}
    (hn : n ≠ 0) (h : (n : ℕ∞) ≤ (F.homDefect G f).order) :
    (n : ℕ∞) ≤ (coordDefect F G hf).val.order ∧
      homogeneousComponent n (coordDefect F G hf).val =
        homogeneousComponent n (F.homDefect G f) := by
  have hv := constantCoeff_evalPoint_add_evalPoint (F := F) (G := G) hf
  have hu : constantCoeff (evalPoint G hf (coordPoint F (0 : Fin 2) + coordPoint F 1)).val =
      0 :=
    constantCoeff_evalPoint hf
      (F.constantCoeff_val_add (constantCoeff_coordPoint _) (constantCoeff_coordPoint _))
  rw [homDefect_eq_val_sub hf] at h ⊢
  have hΨ := G.le_order_val_sub_of_le_order_sub hu hv h
  rw [defectPoint_coord_eq_sub]
  exact ⟨hΨ, G.homogeneousComponent_val_sub hn hv hΨ⟩

variable [F.IsComm]

/-- The leading term of the defect at the coordinate points is a multiple of `C_n`. -/
private theorem exists_homogeneousComponent_defectPoint (hf : PowerSeries.constantCoeff f = 0)
    {n : ℕ} (hn : n ≠ 0)
    (hΨ : (n : ℕ∞) ≤ (coordDefect F G hf).val.order) :
    ∃ c : R, homogeneousComponent n (coordDefect F G hf).val =
      ↑(c • TauCeti.lazardCocycle n R) := by
  refine exists_homogeneousComponent_eq_smul_lazardCocycle F hn hΨ ?_ ?_
  · -- symmetry
    have h := congrArg Subtype.val (defectPoint_eq_substPointHom (G := G) hf
      (coordPoint F (1 : Fin 2)) (coordPoint F 0))
    rw [defectPoint_comm, val_substPointHom, val_coordPoint, val_coordPoint] at h
    exact h.symm.trans (congrArg Subtype.val (coordDefect_eq hf).symm)
  · -- the cocycle identity, up to terms of degree above `n`
    let x (i : Fin 3) : F.Point (Fin 3) := coordPoint F i
    have hx (i : Fin 3) : constantCoeff (x i).val = 0 := constantCoeff_coordPoint i
    have hx01 : constantCoeff (x 0 + x 1).val = 0 := F.constantCoeff_val_add (hx 0) (hx 1)
    have hx12 : constantCoeff (x 1 + x 2).val = 0 := F.constantCoeff_val_add (hx 1) (hx 2)
    have hval (y z : F.Point (Fin 3)) : (defectPoint G hf y z).val =
        (coordDefect F G hf).val.subst ![y.val, z.val] := by
      rw [defectPoint_eq_substPointHom, val_substPointHom]
    have hn' : ((1 : ℕ) : ℕ∞) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have h0 {y z : F.Point (Fin 3)} (hy : constantCoeff y.val = 0)
        (hz : constantCoeff z.val = 0) : constantCoeff (defectPoint G hf y z).val = 0 :=
      order_ne_zero_iff_constCoeff_eq_zero.mp fun h ↦ by
        have := (le_order_defectPoint hf hΨ hy hz).trans_eq h
        exact hn (by exact_mod_cast le_zero_iff.mp this)
    have hA := G.le_order_subst_sub_sub hn (le_order_defectPoint hf hΨ (hx 0) (hx 1))
      (h0 hx01 (hx 2))
    have hC := G.le_order_subst_sub_sub hn (le_order_defectPoint hf hΨ (hx 1) (hx 2))
      (h0 (hx 0) hx12)
    rw [← add_apply, defectPoint_add_defectPoint] at hA
    rw [← add_apply] at hC
    have := le_order_sub hC hA
    have ex (i : Fin 3) : (x i).val = X i := (rfl)
    have e01 : (x 0 + x 1).val = F.toPowerSeries.subst ![X 0, X 1] := by
      rw [FormalGroup.add_apply, ex, ex]
    have e12 : (x 1 + x 2).val = F.toPowerSeries.subst ![X 1, X 2] := by
      rw [FormalGroup.add_apply, ex, ex]
    rw [hval, hval, hval, hval, e01, e12] at this
    simp only [ex] at this
    convert this using 2
    ring

/-- **The leading defect of an approximate homomorphism is a multiple of the Lazard cocycle.**
Let `F` and `G` be commutative formal group laws and let `f` be a power series without constant
term which is a homomorphism from `F` to `G` up to degree `n ≠ 0`: the homomorphism defect
`f(F(X, Y)) - G(f(X), f(Y))` vanishes below degree `n`. Then its degree-`n` part is `c C_n` for
some `c`, where `C_n` is the Lazard cocycle. -/
theorem exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle
    (hf : PowerSeries.constantCoeff f = 0) {n : ℕ} (hn : n ≠ 0)
    (h : (n : ℕ∞) ≤ (F.homDefect G f).order) :
    ∃ c : R, homogeneousComponent n (F.homDefect G f) = ↑(c • TauCeti.lazardCocycle n R) := by
  obtain ⟨hΨ, he⟩ := le_order_defectPoint_coord hf hn h
  obtain ⟨c, hc⟩ := exists_homogeneousComponent_defectPoint hf hn hΨ
  exact ⟨c, he ▸ hc⟩

/-- **The obstruction in degree `pᵏ` is read off the `p`-series.** Let `p` be a prime with
`p = 0` in `R`, let `F` and `G` be commutative formal group laws over `R`, and let `f` be a power
series without constant term whose homomorphism defect `f(F(X, Y)) - G(f(X), f(Y))` vanishes below
degree `n = pᵏ`, `k ≥ 1`. Then the degree-`n` part of the defect is `c C_n`, where `c` is the
coefficient of `Xⁿ` in `[p]_G(f(X)) - f([p]_F(X))`. In particular the defect vanishes in degree
`n` exactly when `f` commutes with multiplication by `p` up to degree `n`. -/
theorem homogeneousComponent_homDefect_eq_smul_lazardCocycle
    (hf : PowerSeries.constantCoeff f = 0) {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0) {k : ℕ}
    (hk : k ≠ 0) (h : ((p ^ k : ℕ) : ℕ∞) ≤ (F.homDefect G f).order) :
    homogeneousComponent (p ^ k) (F.homDefect G f) =
      ↑(PowerSeries.coeff (p ^ k) (PowerSeries.subst f (G.nsmulSeries p) -
          PowerSeries.subst (F.nsmulSeries p) f) • TauCeti.lazardCocycle (p ^ k) R) := by
  have hn : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  obtain ⟨hΨ, he⟩ := le_order_defectPoint_coord hf hn h
  obtain ⟨c, hc⟩ := exists_homogeneousComponent_defectPoint hf hn hΨ
  rw [← he, hc]
  congr 2
  -- compare the degree-`pᵏ` parts of `f([p]_F(X)) - [p]_G(f(X))` and of the sum of the
  -- defects `f(j X + X) - f(j X) - f(X)` over `j < p`
  set x := F.tautologicalPoint
  have hx : constantCoeff x.val = 0 := by
    rw [val_tautologicalPoint]; exact PowerSeries.constantCoeff_X
  have hjx (j : ℕ) : (j • x).val = F.nsmulSeries j := by
    rw [← subst_nsmulSeries, val_tautologicalPoint, PowerSeries.X_subst]
  have hjx₀ (j : ℕ) : constantCoeff (j • x).val = 0 := by
    rw [hjx]; exact F.constantCoeff_nsmulSeries j
  have ht (j : ℕ) (_ : j ∈ Finset.range p) := le_order_defectPoint hf hΨ (hjx₀ j) hx
  have hsum := G.homogeneousComponent_val_sum hn (Finset.range p)
    (fun j ↦ defectPoint G hf (j • x) x) ht
  have hord := G.le_order_val_sum (Finset.range p) (fun j ↦ defectPoint G hf (j • x) x) ht
  rw [← evalPoint_nsmul_sub_nsmul] at hsum hord
  -- the left side
  have hfx : (evalPoint G hf x).val = f := by rw [val_evalPoint, val_tautologicalPoint,
    PowerSeries.X_subst]
  have hpx₀ : constantCoeff (p • evalPoint G hf x).val = 0 := by
    rw [← subst_nsmulSeries, hfx, PowerSeries.subst, constantCoeff_subst_of_constantCoeff_zero
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf).const (fun _ ↦ hf)]
    exact (congrArg _ (G.constantCoeff_nsmulSeries p)).trans (map_zero _)
  have hlhs := G.homogeneousComponent_val_sub hn hpx₀ hord
  rw [val_evalPoint, hjx, ← subst_nsmulSeries, hfx] at hlhs
  -- the right side: the degree-`pᵏ` part of `f(j X + X) - f(j X) - f(X)` is `c C_n(j X, X)`
  have hpX : (p : MvPolynomial Unit R) = 0 := by
    rw [← map_natCast (MvPolynomial.C (σ := Unit)), hpR, map_zero]
  rw [Finset.sum_congr rfl fun j _ ↦ homogeneousComponent_defectPoint_nsmul hf hΨ hc j,
    ← map_sum, ← Finset.smul_sum, TauCeti.sum_aeval_natCast_mul_lazardCocycle hp hpX hk,
    hlhs] at hsum
  have hco := congrArg (coeff (Finsupp.single () (p ^ k))) hsum
  simp only [coeff_homogeneousComponent, Finsupp.degree_single, ↓reduceIte,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_neg, MvPolynomial.coeff_X_pow] at hco
  rw [← PowerSeries.coeff_def Finsupp.single_eq_same] at hco
  rw [← neg_sub, map_neg, hco]
  simp

end Obstruction

end FormalGroup
