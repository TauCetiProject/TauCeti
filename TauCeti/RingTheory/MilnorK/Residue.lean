/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MilnorK.SerreAlgebra
public import TauCeti.RingTheory.Valuation.Discrete.TameSymbol
import TauCeti.Algebra.Ring.Units

/-!
# Serre's map, residues and specializations of Milnor K-theory

Let `v : F → ℤᵐ⁰` be a valuation on a field `F` with valuation ring `𝒪_v` and residue field `k`,
and let `t ∈ Fˣ` have order one, so that every `f ∈ Fˣ` is uniquely `f = u tⁱ` with `u` a unit of
`𝒪_v` and `i = ord_v f`. **Serre's map** sends `f` to `{ū} + i Π` in Serre's algebra
`L(k) = K_*ᴹ(k) ⊕ K_*ᴹ(k) Π` (`TauCeti.SerreAlgebra`). This assignment is additive and kills the
Steinberg products: `d_t(r) d_t(1 - r) = 0` for `r ≠ 0, 1`. The relation `Π Π = {-1} Π` of `L(k)`
is needed for the case `ord_v r < 0`, which reduces to `d_t(x) d_t(-x) = 0`. By the universal
property of the Milnor K-ring it therefore extends to a ring homomorphism
`d_t : K_*ᴹ(F) → L(k)` (`Valuation.serreMap`), which respects the gradings.

Writing `d_t(x) = λ_t(x) + ∂_v(x) Π` with `Π` on the right defines

* the **specialization** `λ_t : K_nᴹ(F) → K_nᴹ(k)` (`Valuation.milnorSpecialization`), a ring
  homomorphism with `λ_t{u₁ t^{i₁}, …, uₙ t^{iₙ}} = {ū₁, …, ūₙ}`; it depends on `t`;
* the **residue** `∂_v : K_{n+1}ᴹ(F) → K_nᴹ(k)` (`Valuation.milnorResidue`), an additive map with
  `∂_v{u₁, …, uₙ, t} = {ū₁, …, ūₙ}` and `∂_v{u₁, …, uₙ} = 0` for units `uᵢ` of `𝒪_v`.

In degree one `∂_v{f} = ord_v f`, and in degree two `∂_v{f, g}` is the tame symbol
`Valuation.tameSymbol`, with no inversion (`Valuation.milnorResidue_ofUnit_mul_ofUnit`). Both maps
are onto in every degree.

Weibel reads the residue off with `Π` on the left, normalized by `{t, u₂, …, uₙ} ↦ {ū₂, …, ūₙ}`;
since `Π y = (-1) ^ (n - 1) y Π` for `y ∈ K_{n-1}ᴹ(k)`, his residue is `(-1) ^ (n - 1) ∂_v` on
`K_nᴹ(F)`.

## Main definitions

* `Valuation.serreMap v t ht`: Serre's ring homomorphism `d_t : K_*ᴹ(F) → L(k)`.
* `Valuation.milnorSpecialization v t ht`: the specialization `λ_t : K_*ᴹ(F) → K_*ᴹ(k)`.
* `Valuation.milnorResidue v t ht`: the residue `∂_v : K_*ᴹ(F) → K_*ᴹ(k)`, lowering degrees by one.

## Main results

* `Valuation.serreMap_ofUnit`: `d_t{f} = {ū} + ord_v f · Π`.
* `Valuation.serreMap_ofUnit_mul_ofUnit`: `d_t{f, g} = {ū_f, ū_g} + {∂_v{f, g}} Π`, where
  `∂_v{f, g}` is the tame symbol.
* `Valuation.C_milnorSpecialization_add_C_milnorResidue_mul_X`: `d_t(x) = λ_t(x) + ∂_v(x) Π`.
* `Valuation.milnorSpecialization_symbol`, `Valuation.milnorResidue_symbol_of_forall_ord_eq_zero`,
  `Valuation.milnorResidue_symbol_append_singleton`: the values on symbols.
* `Valuation.milnorResidue_ofUnit`, `Valuation.milnorResidue_ofUnit_mul_ofUnit`: in degree one the
  residue is the order, in degree two the tame symbol.
* `Valuation.milnorSpecialization_mem_degree`, `Valuation.milnorResidue_mem_degree`: `λ_t`
  preserves degrees and `∂_v` lowers them by one.
* `Valuation.milnorSpecialization_surjOn_degree`, `Valuation.milnorResidue_surjOn_degree`: both maps
  are onto in every degree.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Theorem III.7.3 and its proof.
* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), 318–344, Lemma 2.1,
  where the construction is attributed to Serre.
-/

public section

open TauCeti MilnorK

open scoped WithZero

namespace Valuation

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰) (t : Fˣ) (ht : v.ord (t : F) = 1)

/-! ### Serre's map on units -/

/-- Serre's map on field units, `f ↦ {ū} + ord_v f · Π` with `ū` the reduced unit part. -/
private noncomputable def serreUnit :
    Additive Fˣ →+ SerreAlgebra (IsLocalRing.ResidueField v.valuationSubring) where
  toFun f := SerreAlgebra.C (ofUnit (v.unitPartResidue t ht f.toMul)) +
    v.ord (f.toMul : F) • SerreAlgebra.X
  map_zero' := by simp
  map_add' f g := by
    simp only [toMul_add, map_mul, ofUnit_mul, map_add, Units.val_mul, ord_units_mul, add_smul]
    abel

private theorem serreUnit_apply (f : Fˣ) :
    v.serreUnit t ht (.ofMul f) = SerreAlgebra.C (ofUnit (v.unitPartResidue t ht f)) +
      v.ord (f : F) • SerreAlgebra.X :=
  (rfl)

/-- The product of two values of Serre's map: its `Π`-coefficient is the tame symbol. -/
private theorem serreUnit_mul_serreUnit (f g : Fˣ) :
    v.serreUnit t ht (.ofMul f) * v.serreUnit t ht (.ofMul g) =
      SerreAlgebra.C (ofUnit (v.unitPartResidue t ht f) * ofUnit (v.unitPartResidue t ht g)) +
        SerreAlgebra.C (ofUnit (v.tameSymbol f g)) * SerreAlgebra.X := by
  rw [v.tameSymbol_eq_unitPart t ht]
  ext
  · simp [serreUnit_apply]
  · simp only [serreUnit_apply, SerreAlgebra.snd_mul, SerreAlgebra.snd_add, SerreAlgebra.fst_add,
      SerreAlgebra.snd_C, SerreAlgebra.fst_C, SerreAlgebra.snd_zsmul, SerreAlgebra.fst_zsmul,
      SerreAlgebra.snd_X, SerreAlgebra.fst_X, map_add, map_zsmul, map_one, involute_ofUnit,
      smul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul, ofUnit_mul, ofUnit_zpow,
      mul_smul_comm, smul_mul_assoc, smul_smul, mul_neg, neg_smul]
    rw [mul_comm (v.ord (g : F))]
    abel

/-- The Steinberg relation for reduced unit parts: if `r + s = 1` then `{ū_r, ū_s} = 0` in
`K_2ᴹ(k)`. -/
private theorem ofUnit_mul_ofUnit_unitPartResidue_of_add_eq_one {r s : Fˣ}
    (h : (r : F) + s = 1) :
    ofUnit (v.unitPartResidue t ht r) * ofUnit (v.unitPartResidue t ht s) = 0 := by
  have swap {r s : Fˣ}
      (h : ofUnit (v.unitPartResidue t ht s) * ofUnit (v.unitPartResidue t ht r) = 0) :
      ofUnit (v.unitPartResidue t ht r) * ofUnit (v.unitPartResidue t ht s) = 0 := by
    rw [ofUnit_mul_ofUnit_comm, h, neg_zero]
  have pos {r s : Fˣ} (h : (r : F) + s = 1) (hr : 0 < v.ord (r : F)) :
      ofUnit (v.unitPartResidue t ht r) * ofUnit (v.unitPartResidue t ht s) = 0 := by
    rw [v.unitPartResidue_eq_one_of_add_eq_one t ht h hr, ofUnit_one, mul_zero]
  -- For `ord_v r < 0` write `s = -r (1 - r⁻¹)`, where `1 - r⁻¹` has reduced unit part `1`.
  have neg {r s : Fˣ} (h : (r : F) + s = 1) (hr : v.ord (r : F) < 0) :
      ofUnit (v.unitPartResidue t ht r) * ofUnit (v.unitPartResidue t ht s) = 0 := by
    have hs : s = -r * -(s * r⁻¹) := by
      rw [neg_mul_neg, mul_left_comm, mul_inv_cancel, mul_one]
    rw [hs, map_mul, unitPartResidue_neg, v.unitPartResidue_eq_one_of_add_eq_one t ht
      (Units.val_inv_add_val_neg_mul_inv_eq_one h)
      (by rw [Units.val_inv_eq_inv_val, ord_inv]; omega), mul_one, ofUnit_mul_ofUnit_neg_self]
  have h' : (s : F) + r = 1 := by rw [add_comm, h]
  rcases lt_trichotomy (v.ord (r : F)) 0 with hr | hr | hr
  · exact neg h hr
  · rcases lt_trichotomy (v.ord (s : F)) 0 with hs | hs | hs
    · exact swap (neg h' hs)
    · -- Both entries are units of the valuation ring, whose residues add up to one.
      rw [unitPartResidue_of_ord_eq_zero _ _ _ hr, unitPartResidue_of_ord_eq_zero _ _ _ hs]
      refine ofUnit_mul_ofUnit_of_add_eq_one ?_
      simp only [ValuationSubring.coe_unitGroupToResidueFieldUnits_apply,
        ← IsLocalRing.residue_def, ← map_add, ← map_one (IsLocalRing.residue _)]
      exact congrArg _ (Subtype.ext (by simpa using h))
    · exact swap (pos h' hs)
  · exact pos h hr

/-- **Serre's map kills the Steinberg elements**: `d_t(r) d_t(s) = 0` whenever `r + s = 1`. -/
private theorem serreUnit_mul_serreUnit_of_add_eq_one {r s : Fˣ} (h : (r : F) + s = 1) :
    v.serreUnit t ht (.ofMul r) * v.serreUnit t ht (.ofMul s) = 0 := by
  rw [serreUnit_mul_serreUnit, ofUnit_mul_ofUnit_unitPartResidue_of_add_eq_one v t ht h,
    v.tameSymbol_of_add_eq_one h, ofUnit_one]
  simp

/-! ### Serre's map on the Milnor K-ring -/

/-- **Serre's map** `d_t : K_*ᴹ(F) → L(k)` attached to a valuation `v` and an element `t` of order
one: the ring homomorphism into Serre's algebra over the residue field sending `{u tⁱ}` to
`{ū} + i Π` for every unit `u` of the valuation ring (`Valuation.serreMap_ofUnit`). It is well
defined because `d_t(r) d_t(1 - r) = 0` (`Valuation.serreMap_ofUnit_mul_ofUnit`,
`Valuation.tameSymbol_of_add_eq_one`). -/
noncomputable def serreMap :
    MilnorK F →+* SerreAlgebra (IsLocalRing.ResidueField v.valuationSubring) :=
  MilnorK.lift (v.serreUnit t ht) fun _ _ h ↦ v.serreUnit_mul_serreUnit_of_add_eq_one t ht h

/-- Serre's map on a degree-one class: `d_t{f} = {ū} + ord_v f · Π`, where `f = u t ^ ord_v f`. -/
@[simp]
theorem serreMap_ofUnit (f : Fˣ) :
    v.serreMap t ht (ofUnit f) = SerreAlgebra.C (ofUnit (v.unitPartResidue t ht f)) +
      v.ord (f : F) • SerreAlgebra.X := by
  rw [serreMap, lift_ofUnit, serreUnit_apply]

/-- Serre's map on a symbol of length two: `d_t{f, g} = {ū_f, ū_g} + {∂_v{f, g}} Π`, where
`∂_v{f, g}` is the tame symbol `Valuation.tameSymbol`. -/
theorem serreMap_ofUnit_mul_ofUnit (f g : Fˣ) :
    v.serreMap t ht (ofUnit f * ofUnit g) =
      SerreAlgebra.C (ofUnit (v.unitPartResidue t ht f) * ofUnit (v.unitPartResidue t ht g)) +
        SerreAlgebra.C (ofUnit (v.tameSymbol f g)) * SerreAlgebra.X := by
  rw [map_mul, serreMap_ofUnit, serreMap_ofUnit, ← serreUnit_apply, ← serreUnit_apply,
    serreUnit_mul_serreUnit]

/-- Serre's map sends a symbol of units of the valuation ring to the symbol of their residues. -/
theorem serreMap_symbol_of_forall_ord_eq_zero {l : List Fˣ}
    (hl : ∀ f ∈ l, v.ord (f : F) = 0) :
    v.serreMap t ht (symbol l) = SerreAlgebra.C (symbol (l.map (v.unitPartResidue t ht))) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [symbol_cons, map_mul, ih fun f hf ↦ hl f (List.mem_cons_of_mem a hf), serreMap_ofUnit,
      hl a List.mem_cons_self, zero_smul, add_zero, ← map_mul, List.map_cons, symbol_cons]

/-- Serre's map is graded: it sends `K_nᴹ(F)` into the degree-`n` piece of `L(k)`. -/
theorem serreMap_mem_degree {n : ℕ} {x : MilnorK F} (hx : x ∈ MilnorK.degree F n) :
    v.serreMap t ht x ∈ SerreAlgebra.degree _ n :=
  MilnorK.lift_mem_of_mem_degree _ _ (fun _ ↦ add_mem
    (SerreAlgebra.C_mem_degree (ofUnit_mem_degree_one _))
    (zsmul_mem SerreAlgebra.X_mem_degree_one _)) hx

/-! ### The specialization -/

/-- The **specialization** `λ_t : K_*ᴹ(F) → K_*ᴹ(k)` attached to `v` and an element `t` of order
one: the `Π`-free part of Serre's map `Valuation.serreMap`. It is the ring homomorphism sending
`{u tⁱ}` to `{ū}` (`Valuation.milnorSpecialization_ofUnit`). It depends on the choice of `t`:
replacing `t` by `c t` changes the reduced unit part of `t` from `1` to the residue of `c⁻¹`. -/
noncomputable def milnorSpecialization :
    MilnorK F →+* MilnorK (IsLocalRing.ResidueField v.valuationSubring) :=
  SerreAlgebra.fstHom.comp (v.serreMap t ht)

theorem milnorSpecialization_apply (x : MilnorK F) :
    v.milnorSpecialization t ht x = (v.serreMap t ht x).fst := by
  simp [milnorSpecialization]

/-- `λ_t{u tⁱ} = {ū}`. -/
@[simp]
theorem milnorSpecialization_ofUnit (f : Fˣ) :
    v.milnorSpecialization t ht (ofUnit f) = ofUnit (v.unitPartResidue t ht f) := by
  simp [milnorSpecialization_apply]

/-- `λ_t{u₁ t^{i₁}, …, uₙ t^{iₙ}} = {ū₁, …, ūₙ}`. -/
@[simp]
theorem milnorSpecialization_symbol (l : List Fˣ) :
    v.milnorSpecialization t ht (symbol l) = symbol (l.map (v.unitPartResidue t ht)) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [symbol_cons, ih]

/-- The specialization preserves degrees. -/
theorem milnorSpecialization_mem_degree {n : ℕ} {x : MilnorK F} (hx : x ∈ MilnorK.degree F n) :
    v.milnorSpecialization t ht x ∈ MilnorK.degree _ n := by
  rw [milnorSpecialization_apply]
  exact SerreAlgebra.fst_mem_degree (v.serreMap_mem_degree t ht hx)

/-! ### The residue -/

/-- The **residue** `∂_v : K_*ᴹ(F) → K_*ᴹ(k)` of Milnor K-theory: the coefficient, with `Π` on the
right, of Serre's map `Valuation.serreMap`. It lowers degrees by one
(`Valuation.milnorResidue_mem_degree`), sends `{u₁, …, uₙ, t}` to `{ū₁, …, ūₙ}` and kills symbols
of units of the valuation ring. In degree one it is the order (`Valuation.milnorResidue_ofUnit`)
and in degree two the tame symbol (`Valuation.milnorResidue_ofUnit_mul_ofUnit`). -/
noncomputable def milnorResidue :
    MilnorK F →+ MilnorK (IsLocalRing.ResidueField v.valuationSubring) where
  toFun x := (v.serreMap t ht x).snd
  map_zero' := by simp
  map_add' x y := by simp

theorem milnorResidue_apply (x : MilnorK F) :
    v.milnorResidue t ht x = (v.serreMap t ht x).snd :=
  (rfl)

/-- Serre's map splits as `d_t(x) = λ_t(x) + ∂_v(x) Π`. -/
theorem C_milnorSpecialization_add_C_milnorResidue_mul_X (x : MilnorK F) :
    SerreAlgebra.C (v.milnorSpecialization t ht x) +
      SerreAlgebra.C (v.milnorResidue t ht x) * SerreAlgebra.X = v.serreMap t ht x := by
  rw [milnorSpecialization_apply, milnorResidue_apply, SerreAlgebra.C_fst_add_C_snd_mul_X]

/-- In degree one the residue is the order: `∂_v{f} = ord_v f` in `K_0ᴹ(k) = ℤ`. -/
@[simp]
theorem milnorResidue_ofUnit (f : Fˣ) :
    v.milnorResidue t ht (ofUnit f) = (v.ord (f : F) : MilnorK _) := by
  simp [milnorResidue_apply]

/-- **In degree two the residue is the tame symbol**: `∂_v{f, g} = {∂_v{f, g}}`, with the tame
symbol `Valuation.tameSymbol` read in `K_1ᴹ(k) = kˣ`, and with no inversion. -/
@[simp]
theorem milnorResidue_ofUnit_mul_ofUnit (f g : Fˣ) :
    v.milnorResidue t ht (ofUnit f * ofUnit g) = ofUnit (v.tameSymbol f g) := by
  simp [milnorResidue_apply, serreMap_ofUnit_mul_ofUnit]

/-- The residue of a symbol of units of the valuation ring vanishes: `∂_v{u₁, …, uₙ} = 0`. -/
theorem milnorResidue_symbol_of_forall_ord_eq_zero {l : List Fˣ}
    (hl : ∀ f ∈ l, v.ord (f : F) = 0) : v.milnorResidue t ht (symbol l) = 0 := by
  simp [milnorResidue_apply, v.serreMap_symbol_of_forall_ord_eq_zero t ht hl]

/-- `∂_v{u₁, …, uₙ, t} = {ū₁, …, ūₙ}` for units `uᵢ` of the valuation ring. -/
theorem milnorResidue_symbol_append_singleton {l : List Fˣ}
    (hl : ∀ f ∈ l, v.ord (f : F) = 0) :
    v.milnorResidue t ht (symbol (l ++ [t])) = symbol (l.map (v.unitPartResidue t ht)) := by
  simp [milnorResidue_apply, symbol_append, v.serreMap_symbol_of_forall_ord_eq_zero t ht hl, ht]

/-- The residue lowers degrees by one: it sends `K_{n+1}ᴹ(F)` into `K_nᴹ(k)`. -/
theorem milnorResidue_mem_degree {n : ℕ} {x : MilnorK F} (hx : x ∈ MilnorK.degree F (n + 1)) :
    v.milnorResidue t ht x ∈ MilnorK.degree _ n :=
  (SerreAlgebra.mem_degree_succ.1 (v.serreMap_mem_degree t ht hx)).2

/-- The residue vanishes in degree zero. -/
theorem milnorResidue_of_mem_degree_zero {x : MilnorK F} (hx : x ∈ MilnorK.degree F 0) :
    v.milnorResidue t ht x = 0 :=
  (SerreAlgebra.mem_degree_zero.1 (v.serreMap_mem_degree t ht hx)).2

/-! ### Surjectivity -/

/-- Every symbol over the residue field is the reduction of a symbol of units of the valuation
ring. -/
private theorem exists_symbol_lift (l : List (IsLocalRing.ResidueField v.valuationSubring)ˣ) :
    ∃ l' : List Fˣ, (∀ f ∈ l', v.ord (f : F) = 0) ∧ l'.length = l.length ∧
      l'.map (v.unitPartResidue t ht) = l := by
  induction l with
  | nil => exact ⟨[], by simp⟩
  | cons c l ih =>
    obtain ⟨l', hl', hlen, hmap⟩ := ih
    obtain ⟨u, rfl⟩ := v.valuationSubring.surjective_unitGroupToResidueFieldUnits c
    refine ⟨(u : Fˣ) :: l', ?_, by simp [hlen], by simp [hmap]⟩
    rintro f (_ | ⟨_, hf⟩)
    · exact (v.mem_unitGroup_iff_ord_eq_zero _).1 u.property
    · exact hl' f hf

/-- The specialization maps `K_nᴹ(F)` onto `K_nᴹ(k)`. -/
theorem milnorSpecialization_surjOn_degree (n : ℕ) :
    Set.SurjOn (v.milnorSpecialization t ht) (MilnorK.degree F n)
      (MilnorK.degree (IsLocalRing.ResidueField v.valuationSubring) n) := by
  refine surjOn_degree_of_symbol_mem_image (v.milnorSpecialization t ht).toAddMonoidHom
    fun l hl ↦ ?_
  obtain ⟨l', -, hlen, hmap⟩ := v.exists_symbol_lift t ht l
  exact ⟨symbol l', by simpa [hlen, hl] using symbol_mem_degree l', by simp [hmap]⟩

/-- The specialization is onto. -/
theorem milnorSpecialization_surjective : Function.Surjective (v.milnorSpecialization t ht) :=
  surjective_of_symbol_mem_range (v.milnorSpecialization t ht).toAddMonoidHom fun l ↦ by
    obtain ⟨l', -, -, hmap⟩ := v.exists_symbol_lift t ht l
    exact ⟨symbol l', by simp [hmap]⟩

/-- The residue maps `K_{n+1}ᴹ(F)` onto `K_nᴹ(k)`. -/
theorem milnorResidue_surjOn_degree (n : ℕ) :
    Set.SurjOn (v.milnorResidue t ht) (MilnorK.degree F (n + 1))
      (MilnorK.degree (IsLocalRing.ResidueField v.valuationSubring) n) := by
  refine surjOn_degree_of_symbol_mem_image (v.milnorResidue t ht) fun l hl ↦ ?_
  obtain ⟨l', hl', hlen, hmap⟩ := v.exists_symbol_lift t ht l
  refine ⟨symbol (l' ++ [t]), ?_, by rw [milnorResidue_symbol_append_singleton _ _ _ hl', hmap]⟩
  simpa [hlen, hl] using symbol_mem_degree (l' ++ [t])

/-- The residue is onto. -/
theorem milnorResidue_surjective : Function.Surjective (v.milnorResidue t ht) :=
  surjective_of_symbol_mem_range (v.milnorResidue t ht) fun l ↦ by
    obtain ⟨l', hl', -, hmap⟩ := v.exists_symbol_lift t ht l
    exact ⟨symbol (l' ++ [t]), by rw [milnorResidue_symbol_append_singleton _ _ _ hl', hmap]⟩

end Valuation
