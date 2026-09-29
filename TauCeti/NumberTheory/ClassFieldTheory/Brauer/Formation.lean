/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic

/-!
# The formation of the units of a separable closure

For a field `K` with separable closure `Kˢ` and absolute Galois group `G_K = Gal(Kˢ/K)`, this file
builds the **formation** `unitsFormation K` whose coefficient module is the multiplicative group
`(Kˢ)ˣ`, written additively. Its level at an open subgroup `U` is the unit group of the fixed field
of `U`, and its finite normal layers are the finite Galois extensions `E/F` inside `Kˢ`. It is the
formation on which the local class formation is to be built, and its layers `V ◁ G_K` are the
finite layers of the Brauer group `Br K = H²(G_K, (Kˢ)ˣ)`.

Two of the inputs of the class-formation axioms are proved here, for every field `K`:

* **Hilbert 90 on every finite normal layer** (`subsingleton_h1_unitsFormation`): for open
  subgroups `V ◁ U`, `H¹(U ⧸ V, ((Kˢ)ˣ)^V) = 0`. This is the first class-formation axiom.
* **The finite-layer description of the Brauer group**: the second cohomology of the layer
  `V ◁ G_K` of an open normal subgroup `V` inflates into `Br K` (`brInfl`); the inflation is
  injective (`brInfl_injective`), and every Brauer class is inflated from some layer
  (`exists_brInfl_eq`). This is the map through which the invariant of the Brauer group is to be
  transported to the finite layers.

## Implementation notes

The body of `unitsFormation` is not exposed; its coefficient module is read through the dictionary
`unitsCoeffEquivUnitsFormation`, as `TauCeti.ClassFieldTheory.unitsRep` is read through
`TauCeti.ClassFieldTheory.unitsCoeffEquivUnitsRep`.

The layer `V ◁ U` need not have ground subgroup `G_K`, so its Galois group `U ⧸ V` is not literally
the Galois group of a field extension, and Noether's Hilbert 90 in Mathlib,
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`, does not apply to it as
stated. Rather than transporting a cocycle to the automorphism group of the fixed field of `V`
over that of `U`, `subsingleton_h1_unitsFormation` runs Noether's argument on the layer itself:
the classes of `U ⧸ V` act on the fixed field `E` of `V` through pairwise distinct characters
`E → Kˢ`, because the fixing subgroup of `E` is `V` (`InfiniteGalois.fixingSubgroup_fixedField`),
so Dedekind's independence of characters (`linearIndependent_monoidHom`) provides the
coboundary, exactly as in Mathlib's proof of Noether's theorem.

## Main definitions

* `TauCeti.ClassFieldTheory.unitsFormation K`: the formation of `(Kˢ)ˣ` over `G_K`.
* `TauCeti.ClassFieldTheory.unitsCoeffEquivUnitsFormation K`: its coefficient module as
  `TauCeti.UnitsCoeff K`.
* `TauCeti.ClassFieldTheory.layerBrLevelEquiv V`: the second cohomology of the layer `V ◁ G_K`
  as the explicit `H²(G_K ⧸ V, ((Kˢ)ˣ)^V)` of the finite level `V`.
* `TauCeti.ClassFieldTheory.brInfl V`: inflation from the layer `V ◁ G_K` into `Br K`.

## Main results

* `TauCeti.ClassFieldTheory.mem_level_unitsFormation_iff`: the level of an open subgroup is the
  unit group of its fixed field.
* `TauCeti.ClassFieldTheory.subsingleton_h1_unitsFormation`: `H¹` of every finite normal layer
  vanishes.
* `TauCeti.ClassFieldTheory.brInfl_injective`: inflation from a layer into `Br K` is injective.
* `TauCeti.ClassFieldTheory.exists_brInfl_eq`: every Brauer class is inflated from a layer.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter X, §1, and Chapter XI, §1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open groupCohomology ContCohomology

variable (K : Type) [Field K]

/-- **The formation of the units of a separable closure**: the discrete module `(Kˢ)ˣ`, written
additively as `TauCeti.UnitsCoeff K`, over the absolute Galois group `G_K = Gal(Kˢ/K)`. Its
elements are read through `unitsCoeffEquivUnitsFormation`, and its level at an open subgroup is
the unit group of the fixed field of that subgroup (`mem_level_unitsFormation_iff`). -/
def unitsFormation : Formation (AbsoluteGaloisGroup K) :=
  ⟨ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K),
    ofDiscreteModule_isSmoothDiscrete ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)⟩

/-- **The coefficient dictionary** between `TauCeti.UnitsCoeff K` and the coefficient module of
`unitsFormation K`. It is equivariant by `unitsCoeffEquivUnitsFormation_smul`. -/
def unitsCoeffEquivUnitsFormation : UnitsCoeff K ≃+ (unitsFormation K).toRep.V :=
  AddEquiv.refl _

/-- **The coefficient dictionary is equivariant**: `G_K` acts on the coefficient module of
`unitsFormation K` as it acts on `(Kˢ)ˣ`. -/
@[simp]
theorem unitsCoeffEquivUnitsFormation_smul (g : AbsoluteGaloisGroup K) (x : UnitsCoeff K) :
    unitsCoeffEquivUnitsFormation K (g • x) =
      (unitsFormation K).toRep.ρ g (unitsCoeffEquivUnitsFormation K x) :=
  (rfl)

variable {K}

local notation "Kˢ" => SeparableClosure K

/-! ### Elements of the coefficient module as elements of `Kˢ` -/

/-- An element of the coefficient module of `unitsFormation K`, read as a nonzero element of
`Kˢ`. -/
private def unitsVal (x : (unitsFormation K).toRep.V) : Kˢ :=
  (((unitsCoeffEquivUnitsFormation K).symm x).toMul : Kˢˣ)

private theorem unitsVal_unitsCoeffEquivUnitsFormation (x : UnitsCoeff K) :
    unitsVal (unitsCoeffEquivUnitsFormation K x) = ((x.toMul : Kˢˣ) : Kˢ) :=
  (rfl)

private theorem unitsVal_ρ (g : AbsoluteGaloisGroup K) (x : (unitsFormation K).toRep.V) :
    unitsVal ((unitsFormation K).toRep.ρ g x) = g (unitsVal x) :=
  (rfl)

private theorem unitsVal_zero : unitsVal (0 : (unitsFormation K).toRep.V) = 1 :=
  (rfl)

private theorem unitsVal_add (x y : (unitsFormation K).toRep.V) :
    unitsVal (x + y) = unitsVal x * unitsVal y :=
  (rfl)

private theorem unitsVal_sub (x y : (unitsFormation K).toRep.V) :
    unitsVal (x - y) = unitsVal x / unitsVal y :=
  Units.val_div_eq_div_val _ _

private theorem unitsVal_ne_zero (x : (unitsFormation K).toRep.V) : unitsVal x ≠ 0 :=
  Units.ne_zero _

private theorem unitsVal_injective : Function.Injective (unitsVal (K := K)) :=
  fun _ _ h => (unitsCoeffEquivUnitsFormation K).symm.injective
    (Additive.toMul.injective (Units.ext h))

/-- **The level of an open subgroup `U` is the unit group of its fixed field**: a unit of `Kˢ`
lies in the level `((Kˢ)ˣ)^U` exactly when it lies in the fixed field of `U`. -/
theorem mem_level_unitsFormation_iff {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    {x : UnitsCoeff K} :
    unitsCoeffEquivUnitsFormation K x ∈ (unitsFormation K).level U ↔
      ((x.toMul : Kˢˣ) : Kˢ) ∈ IntermediateField.fixedField U.toSubgroup := by
  rw [Formation.mem_level, IntermediateField.mem_fixedField_iff]
  refine forall₂_congr fun u _ => ?_
  rw [← unitsVal_injective.eq_iff, unitsVal_ρ, unitsVal_unitsCoeffEquivUnitsFormation]

/-! ### Hilbert 90 on the finite normal layers -/

section Hilbert90

variable (L : NormalLayer (AbsoluteGaloisGroup K))

/-- On the fixed field of the top subgroup, the chosen representative of the class of `u` acts as
`u` does. -/
private theorem out_apply_mk {u : L.ground} {z : Kˢ}
    (hz : z ∈ IntermediateField.fixedField L.top.toSubgroup) :
    (((QuotientGroup.mk u : L.Gal).out : L.ground) : AbsoluteGaloisGroup K) z =
      (u : AbsoluteGaloisGroup K) z := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L.relativeTop u
  rw [hh, Subgroup.coe_mul, AlgEquiv.mul_apply]
  congr 1
  exact (IntermediateField.mem_fixedField_iff _ _).1 hz _ (Subgroup.mem_subgroupOf.1 h.2)

/-- Distinct elements of the Galois group of a layer act differently on the fixed field of the
top subgroup, because the top subgroup is closed and so is the fixing subgroup of its fixed
field. -/
private theorem eq_of_out_apply_eq {q q' : L.Gal}
    (h : ∀ z ∈ IntermediateField.fixedField L.top.toSubgroup,
      ((q.out : L.ground) : AbsoluteGaloisGroup K) z =
        ((q'.out : L.ground) : AbsoluteGaloisGroup K) z) :
    q = q' := by
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have hfix : (IntermediateField.fixedField L.top.toSubgroup).fixingSubgroup =
      L.top.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨L.top.toSubgroup, L.top.isClosed⟩
  -- Membership in the open subgroup `L.top` is membership in its underlying subgroup, which
  -- `hfix` rewrites.
  change _ ∈ L.top.toSubgroup
  rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, ← h z hz,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- **Dedekind's independence of characters on a layer**: for coefficients `c` not all zero, some
`z` in the fixed field `E` of the top subgroup has `∑_τ c(τ) τ(z) ≠ 0`, the elements of the
Galois group acting on `E` through pairwise distinct characters `E → Kˢ`. -/
private theorem exists_sum_mul_out_apply_ne_zero {c : L.Gal → Kˢ} (hc : ∃ q, c q ≠ 0) :
    ∃ z ∈ IntermediateField.fixedField L.top.toSubgroup,
      ∑ q, c q * ((q.out : L.ground) : AbsoluteGaloisGroup K) z ≠ 0 := by
  let E := IntermediateField.fixedField L.top.toSubgroup
  let χ : L.Gal → (E →* Kˢ) := fun q =>
    { toFun z := ((q.out : L.ground) : AbsoluteGaloisGroup K) z
      map_one' := by simp
      map_mul' _ _ := by simp }
  have hχ : Function.Injective χ := fun q q' h =>
    eq_of_out_apply_eq L fun z hz => DFunLike.congr_fun h ⟨z, hz⟩
  by_contra! H
  obtain ⟨q, hq⟩ := hc
  exact hq (Fintype.linearIndependent_iff.1 ((linearIndependent_monoidHom E Kˢ).comp χ hχ) c
    (funext fun z => by simpa [χ, Finset.sum_apply] using H z z.2) q)

/-- **Hilbert 90 on a finite normal layer** of the formation of units: for open subgroups
`V ◁ U` of `G_K`, `H¹(U ⧸ V, ((Kˢ)ˣ)^V) = 0`. In field notation, `H¹(Gal(E/F), Eˣ) = 0` for the
finite Galois extension `E/F` of fixed fields of `V` and `U`; this is the first axiom of a class
formation.

This is Noether's argument, as in the proof of Mathlib's
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`: for a `1`-cocycle `f`,
written multiplicatively as `f(στ) = σ(f(τ)) f(σ)`, choose `z` in the fixed field of `V` with
`b = ∑_τ f(τ) τ(z) ≠ 0`; then `σ(b) f(σ) = b` for every `σ`, so `f` is the coboundary of
`b⁻¹`. -/
theorem subsingleton_h1_unitsFormation : Subsingleton (L.H (unitsFormation K) 1) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using H1_induction_on with
  | h f => ?_
  rw [H1π_eq_zero_iff]
  -- The values of the cocycle in `Kˢ`, and the cocycle identity at a representative `s` of `σ`.
  let fv : L.Gal → Kˢ := fun q => unitsVal ((f q : (unitsFormation K).level L.top) : _)
  have hcoc (s : L.ground) (q : L.Gal) :
      fv (QuotientGroup.mk s * q) =
        (s : AbsoluteGaloisGroup K) (fv q) * fv (QuotientGroup.mk s) := by
    simp only [fv]
    rw [(mem_cocycles₁_iff f).1 f.2 (QuotientGroup.mk s) q, Submodule.coe_add, unitsVal_add,
      NormalLayer.rep_ρ_mk_apply_coe, unitsVal_ρ]
  have hf1 : fv 1 = 1 := by
    simp only [fv, cocycles₁_map_one, ZeroMemClass.coe_zero, unitsVal_zero]
  -- The element `b = ∑_τ f(τ) τ(z)`, nonzero for a suitable `z` fixed by the top subgroup.
  obtain ⟨z, hzE, hb0⟩ := exists_sum_mul_out_apply_ne_zero L ⟨1, unitsVal_ne_zero _⟩ (c := fv)
  set b := ∑ q, fv q * ((q.out : L.ground) : AbsoluteGaloisGroup K) z with hb_def
  have hb (s : L.ground) : (s : AbsoluteGaloisGroup K) b * fv (QuotientGroup.mk s) = b := by
    simp only [b, map_sum, map_mul, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk s)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, hcoc]
    have hq : QuotientGroup.mk s * q = QuotientGroup.mk (s * q.out) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    beta_reduce
    rw [hq, out_apply_mk L hzE, Subgroup.coe_mul, AlgEquiv.mul_apply]
    ring
  -- The coboundary is `b⁻¹`, which lies in the top level because the top subgroup fixes `b`.
  let x : UnitsCoeff K := Additive.ofMul (Units.mk0 b hb0)⁻¹
  have hx' : ((x.toMul : Kˢˣ) : Kˢ) = b⁻¹ := by simp [x]
  have hx : unitsVal (unitsCoeffEquivUnitsFormation K x) = b⁻¹ := by
    rw [unitsVal_unitsCoeffEquivUnitsFormation, hx']
  have hxmem : unitsCoeffEquivUnitsFormation K x ∈ (unitsFormation K).level L.top := by
    refine mem_level_unitsFormation_iff.2 <| (IntermediateField.mem_fixedField_iff _ _).2
      fun v hv => ?_
    have hv' := hb ⟨v, L.top_le_ground hv⟩
    rw [(QuotientGroup.eq_one_iff (N := L.relativeTop) _).2 (Subgroup.mem_subgroupOf.2 hv), hf1,
      mul_one] at hv'
    rw [hx', map_inv₀, hv']
  refine ⟨⟨_, hxmem⟩, funext fun σ => ?_⟩
  induction σ using QuotientGroup.induction_on with
  | H s => ?_
  refine Subtype.ext (unitsVal_injective ?_)
  rw [d₀₁_hom_apply, Submodule.coe_sub, NormalLayer.rep_ρ_mk_apply_coe, unitsVal_sub, unitsVal_ρ,
    hx, map_inv₀]
  have hsb : (s : AbsoluteGaloisGroup K) b ≠ 0 := by simpa using hb0
  field_simp
  exact (hb s).symm

end Hilbert90

/-! ### Inflation from the layers of open normal subgroups into the Brauer group -/

section Inflation

variable (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))

/-- The coefficient module of the layer `V ◁ G_K` is the fixed points of `V` in `(Kˢ)ˣ`. -/
private def ofOpenNormalRepEquiv :
    ((NormalLayer.ofOpenNormal V).rep (unitsFormation K)).V ≃ₗ[ℤ]
      FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K) :=
  (LinearEquiv.ofEq _ _ (congrArg (unitsFormation K).level (NormalLayer.top_ofOpenNormal V))).trans
    ((unitsFormation K).levelEquivH0 V.toOpenSubgroup).toIntLinearEquiv

private theorem ofOpenNormalRepEquiv_apply_coe
    (x : ((NormalLayer.ofOpenNormal V).rep (unitsFormation K)).V) :
    ((ofOpenNormalRepEquiv V x : FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K)) :
      UnitsCoeff K) = ((x : (unitsFormation K).level (NormalLayer.ofOpenNormal V).top) :
        (unitsFormation K).toRep.V) :=
  (unitsFormation K).levelEquivH0_apply_coe V.toOpenSubgroup (LinearEquiv.ofEq _ _ _ x)

/-- **The second cohomology of the layer `V ◁ G_K` is that of the finite level `V`**: Mathlib's
`H²(G_K ⧸ V, ((Kˢ)ˣ)^V)` of the layer, carried along `NormalLayer.galOfOpenNormalEquiv`, is the
explicit `H²` of the discrete finite level by
`TauCeti.ContCohomology.explicitH2IsoGroupCohomology`. The coefficient modules are the same
subgroup of `(Kˢ)ˣ`, the level of `V`. -/
def layerBrLevelEquiv :
    (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2 ≃+
      H2 (AbsoluteGaloisGroup K ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup (UnitsCoeff K)) :=
  (groupCohomology.mapIso (NormalLayer.galOfOpenNormalEquiv V) (ofOpenNormalRepEquiv V)
    (fun g => by
      induction g using QuotientGroup.induction_on with
      | H u =>
        refine LinearMap.ext fun x => Subtype.ext ?_
        refine (ofOpenNormalRepEquiv_apply_coe V _).trans
          ((NormalLayer.rep_ρ_mk_apply_coe _ _ u x).trans ?_)
        rw [LinearMap.comp_apply, NormalLayer.galOfOpenNormalEquiv_mk]
        exact congrArg (fun y : UnitsCoeff K => (u : AbsoluteGaloisGroup K) • y)
          (ofOpenNormalRepEquiv_apply_coe V x).symm) 2).toLinearEquiv.toAddEquiv.trans
    (explicitH2IsoGroupCohomology _ _).symm

/-- **Inflation from the layer `V ◁ G_K` into the Brauer group** `Br K = H²(G_K, (Kˢ)ˣ)`: the
identification `layerBrLevelEquiv` of the layer's `H²` with the level of `V`, followed by
`brLevelInfl`. It is injective (`brInfl_injective`), and every Brauer class is inflated from some
layer (`exists_brInfl_eq`). -/
def brInfl : (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2 →+ Br K :=
  (brLevelInfl V).comp (layerBrLevelEquiv V).toAddMonoidHom

/-- `brInfl V` is `brLevelInfl` after the identification `layerBrLevelEquiv`. -/
theorem brInfl_apply (x : (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2) :
    brInfl V x = brLevelInfl V (layerBrLevelEquiv V x) :=
  (rfl)

/-- **Inflation from a layer into the Brauer group is injective**, by Hilbert 90 for `V`
(`brLevelInfl_injective`). -/
theorem brInfl_injective : Function.Injective (brInfl V) :=
  (brLevelInfl_injective V).comp (layerBrLevelEquiv V).injective

variable (K) in
/-- **Every Brauer class is inflated from a layer** `V ◁ G_K` of the formation of units
(`exists_brLevelInfl_eq`). -/
theorem exists_brInfl_eq (x : Br K) :
    ∃ (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
      (y : (NormalLayer.ofOpenNormal V).H (unitsFormation K) 2), brInfl V y = x := by
  obtain ⟨V, y, rfl⟩ := exists_brLevelInfl_eq x
  exact ⟨V, (layerBrLevelEquiv V).symm y, by rw [brInfl_apply, AddEquiv.apply_symm_apply]⟩

end Inflation

end TauCeti.ClassFieldTheory
