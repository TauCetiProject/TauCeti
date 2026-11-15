/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
import TauCeti.NumberTheory.HilbertSymbol.Basic
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Surjective
import TauCeti.NumberTheory.QuadraticForm.Global.Transport
import TauCeti.RingTheory.Norm.Quadratic

/-!
# The global square theorem over a number field

A unit `a ∈ Kˣ` of a number field `K` that becomes a square in the completion `K_v` at every finite
place `v` outside a finite set `S` is already a square in `K` (O'Meara 65:15; Milne, Chapter VIII,
Theorem 1.1 for `n = 2`). No archimedean condition is assumed: local squareness at almost all finite
places forces global squareness, and hence positivity at every real place as well.

This local-to-global principle has three immediate consequences over a number field `K` in any
universe:
* a global unit (or arbitrary field element) is a nonsquare in `K` if and only if it is a nonsquare
  in infinitely many finite completions `K_v`;
* a global field element `x : K` is a square in `K` if and only if its image in `K_v` is a square
  outside finitely many finite places (or at every finite place);
* two classes in `SquareClassGroup K` agree whenever their images in `SquareClassGroup K_v` agree
  outside a finite set of finite places; in particular, the global-to-local map on square-class
  groups across all finite places is injective. This upgrades local discriminant agreement of
  quadratic forms to equality of global discriminants and yields the low-rank cases of the
  Hasse–Minkowski theorem.

## Main results

* `Units.isSquare_of_isSquare_unitAtFinitePlace_of_notMem`: the global square theorem for `Kˣ`
  with a finite exceptional set `S` of finite places.
* `Units.isSquare_iff_forall_isSquare_unitAtFinitePlace`: a unit of `K` is a square iff its
  localization at every finite place is a square.
* `Units.infinite_setOf_not_isSquare_unitAtFinitePlace_iff`: a unit of `K` is a nonsquare iff it
  is a nonsquare at infinitely many finite places.
* `TauCeti.isSquare_of_isSquare_algebraMap_adicCompletion_of_notMem`,
  `TauCeti.isSquare_iff_forall_isSquare_algebraMap_adicCompletion`,
  `TauCeti.infinite_setOf_not_isSquare_algebraMap_adicCompletion_iff`: the corresponding statements
  for arbitrary elements of `K`.
* `TauCeti.eq_zero_of_squareClassMap_adicCompletion_eq_zero_of_notMem`,
  `TauCeti.eq_of_squareClassMap_adicCompletion_eq_of_notMem`,
  `TauCeti.forall_squareClassMap_adicCompletion_eq_zero_iff`,
  `TauCeti.forall_squareClassMap_adicCompletion_eq_iff`,
  `TauCeti.squareClassMap_adicCompletion_injective`: local-to-global triviality, equality, and
  injectivity on `SquareClassGroup K`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 65:15.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, Theorem 1.1, p. 229.
-/

/- In `Type`, the theorem is proved by contradiction through the idele-class norm index. If `a` were
not a square in `K₀`, the quadratic algebra `E = K₀(√a)` would be a cyclic Galois extension of
degree two. At each finite place `v ∉ S`, `a` is a square in `K₀,v`, so `(a_v, u)_v = 1` for every
`u ∈ K₀,vˣ` and the local norm on `(K₀,v ⊗_{K₀} E)ˣ → K₀,vˣ` is surjective. Weak approximation in
local square classes at the finitely many remaining places then makes the idele-class norm map
`C_E → C_{K₀}` surjective
(`TauCeti.GlobalNumberFields.ideleClassNormMap_surjective_of_forall_range_normUnits_eq_top`),
contradicting the first inequality `[E : K₀] ≤ [C_{K₀} : N(C_E)]`
(`TauCeti.ClassFieldTheory.finrank_eq_one_of_surjective_ideleClassNormMap`). Transport along
`Shrink.ringEquiv K` extends the result to number fields in every universe. -/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField TauCeti

universe u

namespace Units

/-- The global square theorem for number fields in `Type`: a unit that is a square in `K_v` at
every finite place outside `S` is a square in `K`. -/
private theorem isSquare_of_isSquare_unitAtFinitePlace_of_notMem_zero
    {K₀ : Type} [Field K₀] [NumberField K₀]
    (a : K₀ˣ) (S : Finset (HeightOneSpectrum (𝓞 K₀)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K₀), v ∉ S → IsSquare (v.unitAtFinitePlace a)) :
    IsSquare a := by
  by_contra ha
  have ha' : ¬IsSquare (a : K₀) := mt Units.isSquare_coe_iff.mp ha
  have : Fact (¬IsSquare (a : K₀)) := ⟨ha'⟩
  have : NumberField (QuadraticAlgebra K₀ (a : K₀) 0) := NumberField.of_module_finite K₀ _
  have hfin : Module.finrank K₀ (QuadraticAlgebra K₀ (a : K₀) 0) = 2 :=
    QuadraticAlgebra.finrank_eq_two (a : K₀) 0
  have : Algebra.IsQuadraticExtension K₀ (QuadraticAlgebra K₀ (a : K₀) 0) := ⟨hfin⟩
  have hθ : (QuadraticAlgebra.omega : QuadraticAlgebra K₀ (a : K₀) 0) ∉
      Set.range (algebraMap K₀ (QuadraticAlgebra K₀ (a : K₀) 0)) := by
    rintro ⟨x, hx⟩
    have := congrArg QuadraticAlgebra.im hx
    simp at this
  have hθ2 : (QuadraticAlgebra.omega : QuadraticAlgebra K₀ (a : K₀) 0) ^ 2 =
      algebraMap K₀ (QuadraticAlgebra K₀ (a : K₀) 0) (a : K₀) := by
    simp [QuadraticAlgebra.omega_pow_two_eq_add, Algebra.algebraMap_eq_smul_one]
  -- Outside `S`, local squareness of `a` makes every `v`-adic unit a norm from `K_v ⊗[K₀] E`.
  have hsurj : Function.Surjective
      (GlobalNumberFields.ideleClassNormMap K₀ (QuadraticAlgebra K₀ (a : K₀) 0)) := by
    refine GlobalNumberFields.ideleClassNormMap_surjective_of_forall_range_normUnits_eq_top S
      fun v hv ↦ eq_top_iff.mpr fun u _ ↦ ?_
    rw [Algebra.mem_range_normUnits_baseChange_iff_exists_sq_sub_mul_sq
      (v.adicCompletion K₀) hθ hθ2 u]
    simpa only [v.unitAtFinitePlace_apply] using
      (hilbertSymbol_eq_one_iff (v.unitAtFinitePlace a) u).mp
        (hilbertSymbol_eq_one_of_isSquare_left (h v hv) u)
  have h1 : Module.finrank K₀ (QuadraticAlgebra K₀ (a : K₀) 0) = 1 :=
    ClassFieldTheory.finrank_eq_one_of_surjective_ideleClassNormMap K₀ _ hsurj
  omega

variable {K : Type u} [Field K] [NumberField K]

/-- **The global square theorem** (O'Meara 65:15). A unit of a number field that is a square in the
completion at all but finitely many finite places is a square in `K`. No archimedean hypothesis is
needed. -/
theorem isSquare_of_isSquare_unitAtFinitePlace_of_notMem
    (a : Kˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsSquare (v.unitAtFinitePlace a)) :
    IsSquare a := by
  classical
  have : Small.{0} K := Module.Finite.small.{0} ℚ K
  let e : Shrink.{0} K ≃+* K := Shrink.ringEquiv K
  have : NumberField (Shrink.{0} K) := .of_ringEquiv K (Shrink.{0} K) e.symm
  let ev := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)
  let a₀ : (Shrink.{0} K)ˣ := Units.map (e.symm : K →* Shrink.{0} K) a
  have ha₀ : Units.map (e : Shrink.{0} K →* K) a₀ = a := Units.ext (e.apply_symm_apply a)
  let S₀ : Finset (HeightOneSpectrum (𝓞 (Shrink.{0} K))) := S.map ev.symm.toEmbedding
  have h₀ : ∀ v₀ : HeightOneSpectrum (𝓞 (Shrink.{0} K)),
      v₀ ∉ S₀ → IsSquare (v₀.unitAtFinitePlace a₀) := by
    intro v₀ hv₀
    rw [← isSquare_unitAtFinitePlace_equivOfRingEquiv e v₀ a₀, ha₀]
    exact h (ev v₀) (by simpa [S₀, ev] using hv₀)
  exact ha₀ ▸ (isSquare_of_isSquare_unitAtFinitePlace_of_notMem_zero a₀ S₀ h₀).map
    (Units.map (e : Shrink.{0} K →* K))

/-- A unit of a number field is a square if and only if its localization at every finite place is a
square. -/
theorem isSquare_iff_forall_isSquare_unitAtFinitePlace (a : Kˣ) :
    IsSquare a ↔ ∀ v : HeightOneSpectrum (𝓞 K), IsSquare (v.unitAtFinitePlace a) :=
  ⟨fun ha v ↦ ha.map v.unitAtFinitePlace,
    fun h ↦ a.isSquare_of_isSquare_unitAtFinitePlace_of_notMem ∅ fun v _ ↦ h v⟩

/-- A unit of a number field fails to be a square at infinitely many finite places if and only if
it is not a global square. -/
@[simp]
theorem infinite_setOf_not_isSquare_unitAtFinitePlace_iff (a : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | ¬IsSquare (v.unitAtFinitePlace a)}.Infinite ↔ ¬IsSquare a := by
  refine ⟨fun hinf ha ↦ ?_, fun ha hfin ↦ ha ?_⟩
  · obtain ⟨v, hv⟩ := hinf.nonempty
    exact hv (ha.map v.unitAtFinitePlace)
  · classical
    exact a.isSquare_of_isSquare_unitAtFinitePlace_of_notMem hfin.toFinset fun v hv ↦
      by_contra fun hns ↦ hv (hfin.mem_toFinset.mpr hns)

end Units

namespace TauCeti

variable {K : Type u} [Field K] [NumberField K]

/-! ### Field elements -/

/-- An element of a number field that becomes a square in the completion at all but finitely many
finite places is a square in `K`. -/
theorem isSquare_of_isSquare_algebraMap_adicCompletion_of_notMem
    (x : K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsSquare (algebraMap K (v.adicCompletion K) x)) :
    IsSquare x := by
  by_cases hx : x = 0
  · exact hx ▸ IsSquare.zero
  · rw [← Units.val_mk0 hx, Units.isSquare_coe_iff]
    refine (Units.mk0 x hx).isSquare_of_isSquare_unitAtFinitePlace_of_notMem S fun v hv ↦ ?_
    rw [← Units.isSquare_coe_iff, v.unitAtFinitePlace_apply, Units.val_mk0]
    exact h v hv

/-- An element of a number field is a square if and only if its image in every finite completion is
a square. -/
theorem isSquare_iff_forall_isSquare_algebraMap_adicCompletion (x : K) :
    IsSquare x ↔ ∀ v : HeightOneSpectrum (𝓞 K), IsSquare (algebraMap K (v.adicCompletion K) x) :=
  ⟨fun hx v ↦ hx.map (algebraMap K (v.adicCompletion K)),
    fun h ↦ isSquare_of_isSquare_algebraMap_adicCompletion_of_notMem x ∅ fun v _ ↦ h v⟩

/-- An element of a number field fails to be a square in infinitely many finite completions if and
only if it is not a square in `K`. -/
@[simp]
theorem infinite_setOf_not_isSquare_algebraMap_adicCompletion_iff (x : K) :
    {v : HeightOneSpectrum (𝓞 K) | ¬IsSquare (algebraMap K (v.adicCompletion K) x)}.Infinite ↔
      ¬IsSquare x := by
  refine ⟨fun hinf hx ↦ ?_, fun hx hfin ↦ hx ?_⟩
  · obtain ⟨v, hv⟩ := hinf.nonempty
    exact hv (hx.map (algebraMap K (v.adicCompletion K)))
  · classical
    exact isSquare_of_isSquare_algebraMap_adicCompletion_of_notMem x hfin.toFinset fun v hv ↦
      by_contra fun hns ↦ hv (hfin.mem_toFinset.mpr hns)

/-! ### The square-class group -/

/-- A global square class that maps to zero in `SquareClassGroup (v.adicCompletion K)` at every
finite place outside a finite set `S` is zero. -/
theorem eq_zero_of_squareClassMap_adicCompletion_eq_zero_of_notMem
    {c : SquareClassGroup K} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (algebraMap K (v.adicCompletion K)).squareClassMap c = 0) :
    c = 0 := by
  let a : Kˣ := Additive.toMul (Quotient.out c)
  have ha : squareClass a = c := squareClass_toMul_out c
  rw [← ha, squareClass_eq_zero_iff]
  refine a.isSquare_of_isSquare_unitAtFinitePlace_of_notMem S fun v hv ↦ ?_
  rw [← squareClass_eq_zero_iff, v.squareClass_unitAtFinitePlace, ha]
  exact h v hv

/-- Two global square classes whose images in `SquareClassGroup (v.adicCompletion K)` agree at every
finite place outside a finite set `S` are equal. -/
theorem eq_of_squareClassMap_adicCompletion_eq_of_notMem
    {c₁ c₂ : SquareClassGroup K} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (algebraMap K (v.adicCompletion K)).squareClassMap c₁ =
        (algebraMap K (v.adicCompletion K)).squareClassMap c₂) :
    c₁ = c₂ := by
  refine sub_eq_zero.mp
    (eq_zero_of_squareClassMap_adicCompletion_eq_zero_of_notMem S fun v hv ↦ ?_)
  rw [map_sub, sub_eq_zero]
  exact h v hv

/-- A global square class maps to zero at every finite place if and only if it is zero. -/
@[simp]
theorem forall_squareClassMap_adicCompletion_eq_zero_iff {c : SquareClassGroup K} :
    (∀ v : HeightOneSpectrum (𝓞 K),
        (algebraMap K (v.adicCompletion K)).squareClassMap c = 0) ↔
      c = 0 :=
  ⟨fun h ↦ eq_zero_of_squareClassMap_adicCompletion_eq_zero_of_notMem ∅ fun v _ ↦ h v,
    fun h _ ↦ h ▸ map_zero _⟩

/-- Two global square classes agree at every finite place if and only if they are equal. -/
@[simp]
theorem forall_squareClassMap_adicCompletion_eq_iff {c₁ c₂ : SquareClassGroup K} :
    (∀ v : HeightOneSpectrum (𝓞 K),
        (algebraMap K (v.adicCompletion K)).squareClassMap c₁ =
          (algebraMap K (v.adicCompletion K)).squareClassMap c₂) ↔
      c₁ = c₂ :=
  ⟨fun h ↦ eq_of_squareClassMap_adicCompletion_eq_of_notMem ∅ fun v _ ↦ h v,
    fun h _ ↦ h ▸ rfl⟩

/-- The global-to-local map from `SquareClassGroup K` to the product of the local square-class
groups across all finite places is injective. -/
theorem squareClassMap_adicCompletion_injective :
    Function.Injective
      (fun (c : SquareClassGroup K) (v : HeightOneSpectrum (𝓞 K)) ↦
        (algebraMap K (v.adicCompletion K)).squareClassMap c) :=
  fun _ _ h ↦ forall_squareClassMap_adicCompletion_eq_iff.mp (congrFun h)

end TauCeti
