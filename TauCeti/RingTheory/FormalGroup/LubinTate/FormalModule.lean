/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.LubinTate.Interpolation
public import TauCeti.RingTheory.FormalGroup.Module.Basic
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The Lubin–Tate formal module

A Lubin–Tate series `f` for a uniformizer `π` over a discrete valuation ring `O` with finite
residue field determines a commutative formal group law and an action of `O` on that law.
The action of `π` is exactly `f`, so the iterates of the given series are the multiplication
maps defining the successive torsion modules.

We use `TauCeti.exists_lubinTate_interpolation`. Composition of its solutions corresponds on
linear terms to matrix multiplication. In particular the two ternary series in the associative
law both interpolate the sum of the three variables.

## References

* J. Lubin and J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81
  (1965), 380–387, §1, Theorem 1.
-/

public section

noncomputable section

namespace TauCeti.IsLubinTateSeries

open MvPowerSeries IsLocalRing

variable {O σ τ : Type*} [CommRing O]

/-- A solution of the interpolation problem for the self-map `f` and linear form `a`. -/
private structure Solution (f : PowerSeries O) (a : σ → O) (H : MvPowerSeries σ O) : Prop where
  const : constantCoeff H = 0
  linear (i : σ) : coeff (Finsupp.single i 1) H = a i
  intertwine : f.subst H = H.subst fun i ↦ f.toMvPowerSeries i

private theorem solution_X [DecidableEq σ] {f : PowerSeries O}
    (hf : f.constantCoeff = 0) (i : σ) :
    Solution f (fun j ↦ if j = i then 1 else 0) (X i) :=
  ⟨constantCoeff_X i, fun j ↦ coeff_index_single_X i j, by
    rw [subst_X (.toMvPowerSeries hf), PowerSeries.toMvPowerSeries_eq_subst]⟩

private theorem Solution.comp [Fintype σ] {f : PowerSeries O}
    (hf : f.constantCoeff = 0) {a : σ → O} {H : MvPowerSeries σ O} (hH : Solution f a H)
    {b : σ → τ → O} {G : σ → MvPowerSeries τ O} (hG : ∀ i, Solution f (b i) (G i)) :
    Solution f (fun j ↦ ∑ i, a i * b i j) (H.subst G) := by
  have hG₀ := fun i ↦ (hG i).const
  have hs := hasSubst_of_constantCoeff_zero hG₀
  refine ⟨constantCoeff_subst_eq_zero hs hG₀ hH.const, fun j ↦ ?_, ?_⟩
  · have hd := congrArg constantCoeff (pderiv_subst hs H j)
    simp only [map_sum, map_mul, constantCoeff_subst_of_constantCoeff_zero hs hG₀,
      Algebra.algebraMap_self_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv,
      zero_add, Finsupp.zero_apply, Nat.cast_zero, mul_one, hH.linear,
      (hG _).linear] at hd
    exact hd
  · rw [← subst_powerSeriesSubst hs (.of_constantCoeff_zero hH.const), hH.intertwine,
      subst_comp_subst_apply (.toMvPowerSeries hf) hs,
      subst_comp_subst_apply hs (.toMvPowerSeries hf)]
    congr 1
    funext i
    rw [PowerSeries.subst_toMvPowerSeries hs, (hG i).intertwine]

private theorem Solution.pair {f : PowerSeries O} (hf : f.constantCoeff = 0)
    {F : MvPowerSeries (Fin 2) O} (hF : Solution f (fun _ ↦ 1) F)
    {a b : τ → O} {x y : MvPowerSeries τ O} (hx : Solution f a x) (hy : Solution f b y) :
    Solution f (fun j ↦ a j + b j) (F.subst ![x, y]) := by
  have h : ∀ i : Fin 2, Solution f (![a, b] i) (![x, y] i) :=
    Fin.forall_fin_two.mpr ⟨hx, hy⟩
  simpa [Fin.sum_univ_two] using hF.comp hf h

private theorem Solution.unary {f : PowerSeries O} (hf : f.constantCoeff = 0)
    {a : O} {u : PowerSeries O} (hu : Solution f (fun _ : Unit ↦ a) u)
    {b : τ → O} {x : MvPowerSeries τ O} (hx : Solution f b x) :
    Solution f (fun j ↦ a * b j) (u.subst x) := by
  simpa [PowerSeries.subst_def] using hu.comp hf (fun _ ↦ hx)

variable [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {f : PowerSeries O}
variable (hf : IsLubinTateSeries π (Nat.card (ResidueField O)) f) (hπ : Irreducible π)

include hf hπ

private theorem existsUnique_solution [Finite σ] (a : σ → O) :
    ∃! H, Solution f a H := by
  have : Finite (ResidueField O) := Nat.finite_of_card_ne_zero hf.exponent_ne_zero
  obtain ⟨H, h, hu, _⟩ := exists_lubinTate_interpolation hπ hf hf (FractionRing O) a
  simp only [← PowerSeries.toMvPowerSeries_eq_subst] at h hu
  exact ⟨H, ⟨h.1, h.2.1, h.2.2⟩, fun G hG ↦ hu G hG.const hG.linear hG.intertwine⟩

private def interpolant [Finite σ] (a : σ → O) : MvPowerSeries σ O :=
  (existsUnique_solution hf hπ a).choose

private theorem solution_interpolant [Finite σ] (a : σ → O) :
    Solution f a (interpolant hf hπ a) :=
  (existsUnique_solution hf hπ a).choose_spec.1

private theorem Solution.eq [Finite σ] {a : σ → O} {H G : MvPowerSeries σ O}
    (hH : Solution f a H) (hG : Solution f a G) : H = G :=
  (existsUnique_solution hf hπ a).unique hH hG

/-- The formal group law determined by a Lubin–Tate series for a uniformizer. -/
def formalGroup : FormalGroup O where
  toPowerSeries := interpolant hf hπ (fun _ ↦ 1)
  zero_constantCoeff := (solution_interpolant hf hπ _).const
  lin_coeff_X := (solution_interpolant hf hπ _).linear 0
  lin_coeff_Y := (solution_interpolant hf hπ _).linear 1
  assoc := by
    have h := solution_interpolant hf hπ (fun _ : Fin 2 ↦ 1)
    have x := solution_X hf.constantCoeff_eq_zero (σ := Fin 3)
    apply Solution.eq hf hπ (h.pair hf.constantCoeff_eq_zero
      (h.pair hf.constantCoeff_eq_zero (x 0) (x 1)) (x 2))
    simpa only [add_assoc] using h.pair hf.constantCoeff_eq_zero (x 0)
      (h.pair hf.constantCoeff_eq_zero (x 1) (x 2))

private theorem solution_formalGroup :
    Solution f (fun _ ↦ 1) (hf.formalGroup hπ).toPowerSeries :=
  solution_interpolant hf hπ _

instance : (hf.formalGroup hπ).IsComm where
  comm := by
    have h := solution_formalGroup hf hπ
    have x := solution_X hf.constantCoeff_eq_zero (σ := Fin 2)
    apply Solution.eq hf hπ h
    convert h.pair hf.constantCoeff_eq_zero (x 1) (x 0) using 1
    funext i
    fin_cases i <;> simp

private def endomorphism (a : O) : FormalGroupHom (hf.formalGroup hπ) (hf.formalGroup hπ) where
  toPowerSeries := interpolant hf hπ (fun _ : Unit ↦ a)
  zero_constantCoeff := (solution_interpolant hf hπ _).const
  hom := by
    have h := solution_formalGroup hf hπ
    have u := solution_interpolant hf hπ (fun _ : Unit ↦ a)
    have x := solution_X hf.constantCoeff_eq_zero (σ := Fin 2)
    apply Solution.eq hf hπ (u.unary hf.constantCoeff_eq_zero h)
    simp only [PowerSeries.toMvPowerSeries_eq_subst]
    have hp := h.pair hf.constantCoeff_eq_zero
      (u.unary hf.constantCoeff_eq_zero (x 0)) (u.unary hf.constantCoeff_eq_zero (x 1))
    convert hp using 1
    · funext i
      fin_cases i <;> simp
    · congr 1
      funext i
      fin_cases i <;> rfl

private theorem solution_endomorphism (a : O) :
    Solution f (fun _ : Unit ↦ a) (endomorphism hf hπ a).toPowerSeries :=
  solution_interpolant hf hπ _

/-- The formal module on the Lubin–Tate law. Its scalar endomorphisms interpolate `aX`. -/
def formalModule : FormalModule O (hf.formalGroup hπ) where
  isComm := inferInstance
  act := endomorphism hf hπ
  coeff_one_act a := (solution_endomorphism hf hπ a).linear ()
  act_one := by
    apply FormalGroupHom.ext
    rw [FormalGroupHom.id_toPowerSeries]
    apply Solution.eq hf hπ (solution_endomorphism hf hπ 1)
    simpa [PowerSeries.X_apply] using solution_X hf.constantCoeff_eq_zero ()
  act_mul a b := by
    apply FormalGroupHom.ext
    rw [FormalGroupHom.comp_toPowerSeries]
    exact Solution.eq hf hπ (solution_endomorphism hf hπ (a * b))
      ((solution_endomorphism hf hπ a).unary hf.constantCoeff_eq_zero
        (solution_endomorphism hf hπ b))
  act_add a b :=
    Solution.eq hf hπ (solution_endomorphism hf hπ (a + b))
      ((solution_formalGroup hf hπ).pair hf.constantCoeff_eq_zero
        (solution_endomorphism hf hπ a) (solution_endomorphism hf hπ b))

/-- The scalar series for `a` is characterized by its tangent coefficient and commutation
with `f` among series fixing the origin. -/
theorem formalModule_act_eq_iff (a : O) (u : PowerSeries O) :
    ((hf.formalModule hπ).act a).toPowerSeries = u ↔
      u.constantCoeff = 0 ∧ u.coeff 1 = a ∧ f.subst u = u.subst f := by
  have hu : Solution f (fun _ : Unit ↦ a) ((hf.formalModule hπ).act a).toPowerSeries :=
    solution_endomorphism hf hπ a
  have hx (i : Unit) : f.toMvPowerSeries i = f := by
    cases i
    rw [PowerSeries.toMvPowerSeries_eq_subst, ← PowerSeries.X_apply, PowerSeries.X_subst]
  constructor
  · rintro rfl
    exact ⟨hu.const, hu.linear (), by simpa only [hx, ← PowerSeries.subst_def] using hu.intertwine⟩
  · rintro ⟨h₀, h₁, h⟩
    apply Solution.eq hf hπ hu
    exact ⟨h₀, fun _ ↦ h₁, by simpa only [hx, ← PowerSeries.subst_def] using h⟩

/-- Multiplication by the uniformizer on the Lubin–Tate formal module is the given series. -/
@[simp]
theorem formalModule_act_uniformizer : ((hf.formalModule hπ).act π).toPowerSeries = f :=
  (hf.formalModule_act_eq_iff hπ π f).2 ⟨hf.constantCoeff_eq_zero, hf.coeff_one, rfl⟩

/-- A formal group law is the Lubin–Tate law of `f` precisely when `f` is an endomorphism. -/
theorem eq_formalGroup_iff (G : FormalGroup O) :
    G = hf.formalGroup hπ ↔ ∃ u : FormalGroupHom G G, u.toPowerSeries = f := by
  refine ⟨fun e ↦ e ▸ ⟨(hf.formalModule hπ).act π, hf.formalModule_act_uniformizer hπ⟩, ?_⟩
  rintro ⟨u, rfl⟩
  apply FormalGroup.ext
  apply Solution.eq hf hπ _ (solution_formalGroup hf hπ)
  exact ⟨G.zero_constantCoeff, Fin.forall_fin_two.mpr ⟨G.lin_coeff_X, G.lin_coeff_Y⟩, u.hom⟩

/-- On the Lubin–Tate law the action of the uniformizer determines the entire scalar action. -/
theorem eq_formalModule_iff (ρ : FormalModule O (hf.formalGroup hπ)) :
    ρ = hf.formalModule hπ ↔ (ρ.act π).toPowerSeries = f := by
  refine ⟨fun e ↦ e ▸ hf.formalModule_act_uniformizer hπ, fun h ↦ ?_⟩
  apply FormalModule.ext
  intro a
  symm
  apply (hf.formalModule_act_eq_iff hπ a _).2
  refine ⟨(ρ.act a).zero_constantCoeff, ρ.coeff_one_act a, ?_⟩
  simpa only [FormalGroupHom.comp_toPowerSeries, h] using
    congrArg FormalGroupHom.toPowerSeries (ρ.act_comp_act_comm π a)

/-- On the special fibre multiplication by `π ^ m` is the power map `X ↦ X ^ (q ^ m)`,
where `q` is the residue cardinality. -/
@[simp]
theorem map_residue_formalModule_act_uniformizer_pow (m : ℕ) :
    ((hf.formalModule hπ).act (π ^ m)).toPowerSeries.map (residue O) =
      PowerSeries.X ^ (Nat.card (ResidueField O) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, FormalModule.act_mul, ← FormalGroupHom.map_toPowerSeries,
      FormalGroupHom.map_comp, FormalGroupHom.comp_toPowerSeries]
    simp only [FormalGroupHom.map_toPowerSeries, hf.formalModule_act_uniformizer,
      hf.map_residue, ih]
    have hs : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries (ResidueField O)) ^
        Nat.card (ResidueField O)) := .X_pow hf.exponent_ne_zero
    rw [PowerSeries.subst_pow hs, PowerSeries.subst_X hs, ← pow_mul, pow_succ']

section BaseChange

variable {O' : Type*} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
  (φ : O →+* O')
  (hf' : IsLubinTateSeries (φ π) (Nat.card (ResidueField O')) (f.map φ))
  (hπ' : Irreducible (φ π))

/-- Base change of the Lubin–Tate law when the image series is Lubin–Tate for the
image uniformizer. -/
theorem map_formalGroup : (hf.formalGroup hπ).map φ = hf'.formalGroup hπ' := by
  apply (hf'.eq_formalGroup_iff hπ' _).2
  exact ⟨((hf.formalModule hπ).act π).map φ, by simp⟩

/-- In the base-changed coordinate, the scalar series for `φ a` is the image of that for `a`. -/
theorem map_formalModule_act (a : O) :
    ((hf.formalModule hπ).act a).toPowerSeries.map φ =
      ((hf'.formalModule hπ').act (φ a)).toPowerSeries := by
  let u := (hf.formalModule hπ).act a
  apply ((hf'.formalModule_act_eq_iff hπ' (φ a) _).2 ?_).symm
  refine ⟨by simpa only [FormalGroupHom.map_toPowerSeries] using (u.map φ).zero_constantCoeff,
    ?_, ?_⟩
  · simp only [PowerSeries.coeff_map, FormalModule.coeff_one_act, Algebra.algebraMap_self_apply]
  · simpa only [FormalGroupHom.map_comp, FormalGroupHom.comp_toPowerSeries,
      FormalGroupHom.map_toPowerSeries, hf.formalModule_act_uniformizer] using
      congrArg (fun v ↦ (v.map φ).toPowerSeries) ((hf.formalModule hπ).act_comp_act_comm π a)

end BaseChange

end TauCeti.IsLubinTateSeries

namespace TauCeti

open IsLocalRing

/-- The Lubin–Tate theorem. A Lubin–Tate series `f` for a uniformizer `π` determines a formal
group law with a formal module structure on which `π` acts by `f`. It is the unique formal group
law admitting `f` as an endomorphism. -/
theorem exists_formalModule_of_isLubinTateSeries {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {f : PowerSeries O}
    (hf : IsLubinTateSeries π (Nat.card (ResidueField O)) f) :
    ∃ (F : FormalGroup O) (ρ : FormalModule O F), (ρ.act π).toPowerSeries = f ∧
      ∀ (G : FormalGroup O) (φ : FormalGroupHom G G), φ.toPowerSeries = f → G = F :=
  ⟨hf.formalGroup hπ, hf.formalModule hπ, hf.formalModule_act_uniformizer hπ,
    fun G φ h ↦ (hf.eq_formalGroup_iff hπ G).2 ⟨φ, h⟩⟩

end TauCeti
