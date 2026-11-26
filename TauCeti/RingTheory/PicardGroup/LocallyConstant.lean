/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Hom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.PicardGroup.Prod
public import TauCeti.Topology.LocallyConstant.ClopenRingHom
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.Topology.LocallyConstant.CharFn

/-!
# Locally constant powers of Picard classes

Let `R` be a commutative ring and `H(R) = LocallyConstant (Spec R) ℤ` the ring of locally
constant integer functions on its prime spectrum. A Picard class `L` can be raised to a power
`f ∈ H(R)`: since `Spec R` is compact, `f` takes finitely many values `n`, on clopen fibres
`f⁻¹{n}`, and `L ^ f` is the class which is `L ^ n` on the fibre `f⁻¹{n}`. These locally constant
exponents are needed because the rank of a finite projective module is a locally constant
function rather than an integer, and the determinant of a product of `K₀`-classes involves the
determinants of the factors raised to the ranks of the others.

The construction glues classes along clopen subsets. For an idempotent `e` of `R`, the Picard
group splits as `Pic R ≃* Pic (R ⧸ (1 - e)) × Pic (R ⧸ (e))`, the restrictions to the clopen
basic open set `U = D(e) = {p | e ∉ p}` and to its complement. The class
`CommRing.Pic.mulIndicator he L` is `L` on `U` and trivial on the complement, like
`Set.mulIndicator`. It is characterised by its base changes: along a ring map `ψ` with `ψ e = 1`
it becomes the base change of `L`, and along one with `ψ e = 0` it becomes trivial. The
endomorphisms `mulIndicator` of the additive group `Additive (Pic R)` form a homomorphism of
Boolean algebras from the clopen subsets of `Spec R` to the idempotent endomorphisms, so
`LocallyConstant.ringHomOfClopens` extends them to a ring homomorphism
`H(R) →+* Module.End ℤ (Additive (Pic R))`. This makes the additive Picard group an
`H(R)`-module. The power `L ^ f` is `f • Additive.ofMul L`, and the exponent laws
`L ^ (f + g) = L ^ f L ^ g`, `L ^ (f g) = (L ^ g) ^ f`, `L ^ 0 = 1`, `L ^ 1 = L`,
`(L M) ^ f = L ^ f M ^ f` and `(L⁻¹) ^ f = (L ^ f)⁻¹` are the module axioms. On constant
functions the action is the usual power.

## Main definitions

* `CommRing.Pic.mulIndicator`: for an idempotent `e`, the endomorphism of `Pic R` sending `L` to
  the class which is `L` on `D(e)` and trivial on its complement.
* `CommRing.Pic.locallyConstantToEnd`: the ring homomorphism `H(R) →+* Module.End ℤ (Additive
  (Pic R))` sending the characteristic function `χ_U` of a clopen set to `mulIndicator`.
* `CommRing.Pic.instModuleLocallyConstantAdditive`: the resulting `H(R)`-module structure on the
  additive Picard group.

## Main results

* `CommRing.Pic.mapRingHom_mulIndicator_of_map_eq_one`,
  `CommRing.Pic.mapRingHom_mulIndicator_of_map_eq_zero`: the base changes of `mulIndicator he L`
  along ring maps sending `e` to `1` and to `0`.
* `CommRing.Pic.mapRingHom_mulIndicator`: `mulIndicator` commutes with arbitrary base change.
* `CommRing.Pic.mulIndicator_isIdempotentElem_one_apply`,
  `CommRing.Pic.mulIndicator_isIdempotentElem_zero_apply`, `CommRing.Pic.mulIndicator_mulIndicator`
  and `CommRing.Pic.mulIndicator_mul_mulIndicator_one_sub`: the Boolean algebra identities.
* `CommRing.Pic.charFn_smul`, `CommRing.Pic.charFn_isIdempotentElemEquivClopens_smul`: the
  characteristic function of a clopen set `U` acts by `mulIndicator` of the idempotent of `U`.
* `CommRing.Pic.smul_ofMul_eq_prod`: `L ^ f` is the product of the classes `L ^ n` placed on the
  fibres `f⁻¹{n}`.
* `CommRing.Pic.mapRingHom_smul`: base change along `ψ : R →+* S` sends `L ^ f` to
  `ψ(L) ^ (f ∘ Spec ψ)`; in particular `L ^ f` restricts to the same construction on a clopen
  subset.
* `CommRing.Pic.mapRingHom_smul_of_forall_eq`: if `f` is constantly `n` on the image of
  `Spec S → Spec R`, the base change of `L ^ f` to `S` is the `n`-th power of the base change of
  `L`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145, AMS, 2013, Chapter I, Section 3 (Picard groups and the determinant of a
  projective module of nonconstant rank) and Chapter II, Section 2 (the ring `H₀(R)` of locally
  constant ranks).
-/

public section

open TopologicalSpace PrimeSpectrum
open Ideal.Quotient (mk_singleton_self)
open TauCeti.Ideal.Quotient (mk_span_singleton_one_sub_self)

namespace CommRing.Pic

universe u v

variable {R : Type u} [CommRing R] {e : R}

/-! ### Extending a Picard class by the trivial class off a clopen set -/

/-- For an idempotent `e` of `R`, the class `mulIndicator he L` is `L` on the clopen set `D(e)`
of `Spec R` and the trivial class on its complement: under the splitting
`Pic R ≃* Pic (R ⧸ (1 - e)) × Pic (R ⧸ (e))` it corresponds to `(L|_{D(e)}, 1)`. Like
`Set.mulIndicator`, it keeps a value on a set and replaces it by `1` elsewhere. -/
noncomputable def mulIndicator (he : IsIdempotentElem e) : Pic R →* Pic R :=
  (prodEquivOfIsIdempotentElem he).symm.toMonoidHom.comp <| (MonoidHom.inl _ _).comp <|
    (MonoidHom.fst _ _).comp (prodEquivOfIsIdempotentElem he).toMonoidHom

/-- Under the splitting `Pic R ≃* Pic (R ⧸ (1 - e)) × Pic (R ⧸ (e))`, the class
`mulIndicator he L` is `(L|_{D(e)}, 1)`. -/
theorem prodEquivOfIsIdempotentElem_mulIndicator (he : IsIdempotentElem e) (L : Pic R) :
    prodEquivOfIsIdempotentElem he (mulIndicator he L) =
      (mapAlgebra R (R ⧸ Ideal.span {1 - e}) L, 1) := by
  simp [mulIndicator]

/-- `mulIndicator he` only depends on the idempotent `e`. -/
theorem mulIndicator_congr {f : R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : e = f) : mulIndicator he = mulIndicator hf := by
  subst h
  rfl

section Semiring

variable {S : Type v} [CommSemiring S]

/-- Along a ring map `ψ` with `ψ e = 1`, that is, whose spectrum lands in `D(e)`, the class
`mulIndicator he L` has the same base change as `L`. -/
theorem mapRingHom_mulIndicator_of_map_eq_one (he : IsIdempotentElem e) {ψ : R →+* S}
    (h : ψ e = 1) (L : Pic R) : mapRingHom ψ (mulIndicator he L) = mapRingHom ψ L := by
  have h₁ : ψ (1 - e) = 0 := by
    rw [← mul_one (ψ (1 - e)), ← h, ← map_mul, he.one_sub_mul_self, map_zero]
  have hker : ∀ a ∈ Ideal.span {1 - e}, ψ a = 0 := fun a ha ↦ by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, h₁, mul_zero]
  rw [← Ideal.Quotient.lift_comp_mk _ ψ hker, ← mapRingHom_mapRingHom, ← mapRingHom_mapRingHom,
    ← Ideal.Quotient.algebraMap_eq, mapRingHom_algebraMap]
  congr 1
  simpa using congr_arg Prod.fst (prodEquivOfIsIdempotentElem_mulIndicator he L)

/-- Along a ring map `ψ` with `ψ e = 0`, that is, whose spectrum lands in the complement of
`D(e)`, the class `mulIndicator he L` becomes trivial. -/
theorem mapRingHom_mulIndicator_of_map_eq_zero (he : IsIdempotentElem e) {ψ : R →+* S}
    (h : ψ e = 0) (L : Pic R) : mapRingHom ψ (mulIndicator he L) = 1 := by
  have hker : ∀ a ∈ Ideal.span {e}, ψ a = 0 := fun a ha ↦ by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, h, mul_zero]
  have h₂ : mapAlgebra R (R ⧸ Ideal.span {e}) (mulIndicator he L) = 1 := by
    simpa using congr_arg Prod.snd (prodEquivOfIsIdempotentElem_mulIndicator he L)
  rw [← Ideal.Quotient.lift_comp_mk _ ψ hker, ← mapRingHom_mapRingHom,
    ← Ideal.Quotient.algebraMap_eq, mapRingHom_algebraMap, h₂, map_one]

end Semiring

variable {S : Type v} [CommRing S]

/-- `mulIndicator` commutes with base change: along any ring map `ψ : R →+* S`, the base change
of `mulIndicator he L` is `mulIndicator` of `ψ e` applied to the base change of `L`. -/
@[simp]
theorem mapRingHom_mulIndicator (he : IsIdempotentElem e) (ψ : R →+* S) (L : Pic R) :
    mapRingHom ψ (mulIndicator he L) = mulIndicator (he.map ψ) (mapRingHom ψ L) := by
  refine ext_of_isIdempotentElem (he.map ψ) ?_ ?_ <;> rw [mapRingHom_mapRingHom]
  · rw [mapRingHom_mulIndicator_of_map_eq_one (ψ := (Ideal.Quotient.mk _).comp ψ) he
        (mk_span_singleton_one_sub_self (ψ e)),
      mapRingHom_mulIndicator_of_map_eq_one _ (mk_span_singleton_one_sub_self (ψ e)),
      mapRingHom_mapRingHom]
  · rw [mapRingHom_mulIndicator_of_map_eq_zero (ψ := (Ideal.Quotient.mk _).comp ψ) he
        (mk_singleton_self (ψ e)),
      mapRingHom_mulIndicator_of_map_eq_zero _ (mk_singleton_self (ψ e))]

/-- On the whole spectrum, `mulIndicator` is the identity. -/
@[simp]
theorem mulIndicator_isIdempotentElem_one_apply (L : Pic R) :
    mulIndicator (.one : IsIdempotentElem (1 : R)) L = L := by
  simpa [mapRingHom_id_apply] using
    mapRingHom_mulIndicator_of_map_eq_one (ψ := RingHom.id R) .one (map_one _) L

/-- On the empty clopen set, `mulIndicator` is trivial. -/
@[simp]
theorem mulIndicator_isIdempotentElem_zero_apply (L : Pic R) :
    mulIndicator (.zero : IsIdempotentElem (0 : R)) L = 1 := by
  simpa [mapRingHom_id_apply] using
    mapRingHom_mulIndicator_of_map_eq_zero (ψ := RingHom.id R) .zero (map_zero _) L

/-- The composite of the indicators of `e` and `f` is the indicator of the product `e f`, whose
clopen set `D(e f)` is the intersection of `D(e)` and `D(f)`. -/
theorem mulIndicator_mulIndicator {f : R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (L : Pic R) : mulIndicator he (mulIndicator hf L) = mulIndicator (he.mul hf) L := by
  refine ext_of_isIdempotentElem he ?_ ?_
  · rw [mapRingHom_mulIndicator_of_map_eq_one _ (mk_span_singleton_one_sub_self e),
      mapRingHom_mulIndicator, mapRingHom_mulIndicator]
    congr 1
    exact mulIndicator_congr _ _ (by simp)
  · rw [mapRingHom_mulIndicator_of_map_eq_zero _ (mk_singleton_self e),
      mapRingHom_mulIndicator_of_map_eq_zero _ (by simp [mk_singleton_self])]

/-- The indicators of the complementary clopen sets `D(e)` and `D(1 - e)` multiply to the
class itself. -/
theorem mulIndicator_mul_mulIndicator_one_sub (he : IsIdempotentElem e) (L : Pic R) :
    mulIndicator he L * mulIndicator he.one_sub L = L := by
  refine ext_of_isIdempotentElem he ?_ ?_ <;> rw [map_mul]
  · rw [mapRingHom_mulIndicator_of_map_eq_one _ (mk_span_singleton_one_sub_self e),
      mapRingHom_mulIndicator_of_map_eq_zero _ (by simp), mul_one]
  · rw [mapRingHom_mulIndicator_of_map_eq_zero _ (mk_singleton_self e),
      mapRingHom_mulIndicator_of_map_eq_one _ (by simp [mk_singleton_self]), one_mul]

/-! ### The `H(R)`-module structure on the additive Picard group -/

/-- The indicator endomorphism of the additive Picard group attached to a clopen subset `U` of
`Spec R`, through the idempotent `e_U` with `D(e_U) = U`. -/
private noncomputable def clopenEnd (U : Clopens (PrimeSpectrum R)) :
    Module.End ℤ (Additive (Pic R)) :=
  (mulIndicator (isIdempotentElemEquivClopens.symm U).prop).toAdditive.toIntLinearMap

private theorem clopenEnd_apply (U : Clopens (PrimeSpectrum R)) (x : Additive (Pic R)) :
    clopenEnd U x = .ofMul (mulIndicator (isIdempotentElemEquivClopens.symm U).prop x.toMul) :=
  rfl

private theorem clopenEnd_top : clopenEnd (⊤ : Clopens (PrimeSpectrum R)) = 1 := by
  refine LinearMap.ext fun x ↦ ?_
  rw [clopenEnd_apply, mulIndicator_congr _ .one
      (congr_arg Subtype.val isIdempotentElemEquivClopens_symm_top),
    mulIndicator_isIdempotentElem_one_apply, ofMul_toMul, one_apply_eq_self]

private theorem clopenEnd_inf (U V : Clopens (PrimeSpectrum R)) :
    clopenEnd (U ⊓ V) = clopenEnd U * clopenEnd V := by
  refine LinearMap.ext fun x ↦ ?_
  rw [mul_apply_eq_comp, clopenEnd_apply, clopenEnd_apply, clopenEnd_apply, toMul_ofMul,
    mulIndicator_congr _ ((isIdempotentElemEquivClopens.symm U).prop.mul
      (isIdempotentElemEquivClopens.symm V).prop)
      (congr_arg Subtype.val (isIdempotentElemEquivClopens_symm_inf U V)),
    ← mulIndicator_mulIndicator]

private theorem clopenEnd_compl (U : Clopens (PrimeSpectrum R)) :
    clopenEnd Uᶜ = 1 - clopenEnd U := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.sub_apply, one_apply_eq_self, eq_sub_iff_add_eq', clopenEnd_apply,
    clopenEnd_apply, ← ofMul_mul, mulIndicator_congr (isIdempotentElemEquivClopens.symm Uᶜ).prop
      (isIdempotentElemEquivClopens.symm U).prop.one_sub
      (congr_arg Subtype.val (isIdempotentElemEquivClopens_symm_compl U)),
    mulIndicator_mul_mulIndicator_one_sub, ofMul_toMul]

/-- The ring homomorphism `H(R) →+* Module.End ℤ (Additive (Pic R))` through which locally
constant integer functions act on the additive Picard group: it sends the characteristic function
of a clopen set `U` to `mulIndicator` of the idempotent `e_U` with `D(e_U) = U`. -/
noncomputable def locallyConstantToEnd :
    LocallyConstant (PrimeSpectrum R) ℤ →+* Module.End ℤ (Additive (Pic R)) :=
  LocallyConstant.ringHomOfClopens clopenEnd_top clopenEnd_inf clopenEnd_compl

/-- **Locally constant powers of Picard classes.** The additive Picard group of `R` is a module
over the ring `H(R) = LocallyConstant (Spec R) ℤ`: the characteristic function of a clopen set `U`
acts by `mulIndicator` of the idempotent of `U` (`CommRing.Pic.charFn_smul`), and `f` acts on
`Additive.ofMul L` by placing `L ^ n` on each fibre `f⁻¹{n}` (`CommRing.Pic.smul_ofMul_eq_prod`).
The locally constant power `L ^ f` is `f • Additive.ofMul L`. -/
noncomputable instance instModuleLocallyConstantAdditive :
    Module (LocallyConstant (PrimeSpectrum R) ℤ) (Additive (Pic R)) :=
  Module.compHom _ locallyConstantToEnd

/-- `CommRing.Pic.locallyConstantToEnd f` is the action of `f` on the additive Picard group. -/
theorem locallyConstantToEnd_apply (f : LocallyConstant (PrimeSpectrum R) ℤ)
    (x : Additive (Pic R)) : locallyConstantToEnd f x = f • x :=
  rfl

/-- The characteristic function of a clopen set `U` acts by `mulIndicator` of the idempotent
`e_U` with `D(e_U) = U`. -/
@[simp]
theorem charFn_smul (U : Clopens (PrimeSpectrum R)) (x : Additive (Pic R)) :
    LocallyConstant.charFn ℤ U.isClopen • x =
      .ofMul (mulIndicator (isIdempotentElemEquivClopens.symm U).prop x.toMul) := by
  rw [← locallyConstantToEnd_apply, locallyConstantToEnd, LocallyConstant.ringHomOfClopens_charFn,
    clopenEnd_apply]

/-- The characteristic function of the clopen set `D(e)` of an idempotent `e` acts by
`mulIndicator he`. -/
theorem charFn_isIdempotentElemEquivClopens_smul (he : IsIdempotentElem e) (x : Additive (Pic R)) :
    LocallyConstant.charFn ℤ (isIdempotentElemEquivClopens ⟨e, he⟩).isClopen • x =
      .ofMul (mulIndicator he x.toMul) := by
  rw [charFn_smul, mulIndicator_congr _ he (by rw [OrderIso.symm_apply_apply])]

/-- **Locally constant powers on fibres.** `L ^ f` is the product, over any finite set of integers
containing the values of `f`, of the classes which are `L ^ n` on the fibre `f⁻¹{n}` and trivial
elsewhere. -/
theorem smul_ofMul_eq_prod (f : LocallyConstant (PrimeSpectrum R) ℤ) {s : Finset ℤ}
    (hs : Set.range f ⊆ s) (L : Pic R) :
    f • Additive.ofMul L = .ofMul (∏ n ∈ s,
      mulIndicator (isIdempotentElemEquivClopens.symm (f.fiberClopens n)).prop (L ^ n)) := by
  rw [← locallyConstantToEnd_apply, locallyConstantToEnd,
    LocallyConstant.ringHomOfClopens_apply _ _ _ f hs,
    LinearMap.sum_apply, ofMul_prod]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [LinearMap.smul_apply, clopenEnd_apply, toMul_ofMul, map_zpow, ofMul_zpow]

/-- Constant exponents act by the usual powers: `L ^ n` for the constant function `n`. -/
@[simp]
theorem const_smul_ofMul (n : ℤ) (L : Pic R) :
    LocallyConstant.const (PrimeSpectrum R) n • Additive.ofMul L = .ofMul (L ^ n) := by
  have hn : LocallyConstant.const (PrimeSpectrum R) n = n := LocallyConstant.ext fun p ↦ by
    rw [← LocallyConstant.evalRingHom_apply (Y := ℤ) p (n : LocallyConstant _ ℤ), map_intCast,
      Int.cast_id, LocallyConstant.coe_const, Function.const_apply]
  rw [ofMul_zpow, ← Int.cast_smul_eq_zsmul (LocallyConstant (PrimeSpectrum R) ℤ), hn]

/-- **Base change of locally constant powers.** Along a ring map `ψ : R →+* S`, the base change of
`L ^ f` is `ψ(L) ^ (f ∘ Spec ψ)`. For the quotient `R → R ⧸ (1 - e)` by an idempotent this says
that `L ^ f` restricts on the clopen set `D(e)` to the same construction there. -/
theorem mapRingHom_smul (ψ : R →+* S) (f : LocallyConstant (PrimeSpectrum R) ℤ)
    (x : Additive (Pic R)) :
    (mapRingHom ψ).toAdditive (f • x) =
      f.comap ⟨comap ψ, continuous_comap ψ⟩ • (mapRingHom ψ).toAdditive x := by
  let φ : LocallyConstant (PrimeSpectrum R) ℤ →+ Additive (Pic S) :=
    ((mapRingHom ψ).toAdditive : Additive (Pic R) →+ _).comp ((smulAddHom _ _).flip x)
  let φ' : LocallyConstant (PrimeSpectrum R) ℤ →+ Additive (Pic S) :=
    ((smulAddHom _ _).flip ((mapRingHom ψ).toAdditive x)).comp
      (LocallyConstant.comapAddMonoidHom ⟨comap ψ, continuous_comap ψ⟩)
  refine DFunLike.congr_fun (LocallyConstant.addMonoidHom_ext_charFn (φ := φ) (ψ := φ') ?_) f
  intro U
  -- Write `U = D(e)`; then `Spec ψ` pulls `D(e)` back to `D(ψ e)` (`comap_basicOpen`).
  obtain ⟨⟨e, he⟩, rfl⟩ := isIdempotentElemEquivClopens.surjective U
  have hV : (LocallyConstant.charFn ℤ (isIdempotentElemEquivClopens ⟨e, he⟩).isClopen).comap
      ⟨comap ψ, continuous_comap ψ⟩ =
      LocallyConstant.charFn ℤ (isIdempotentElemEquivClopens ⟨ψ e, he.map ψ⟩).isClopen := by
    have h : comap ψ ⁻¹' (isIdempotentElemEquivClopens ⟨e, he⟩ : Set (PrimeSpectrum R)) =
        isIdempotentElemEquivClopens ⟨ψ e, he.map ψ⟩ :=
      congr_arg SetLike.coe (comap_basicOpen ψ e)
    simp only [LocallyConstant.comap_charFn, ContinuousMap.coe_mk, h]
  simp only [φ, φ', AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, smulAddHom_apply,
    LocallyConstant.comapAddMonoidHom_apply, hV, charFn_isIdempotentElemEquivClopens_smul,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, mapRingHom_mulIndicator]

/-- **Restriction to a fibre.** If `f` is constantly `n` on the image of `Spec S → Spec R`, for
instance on the clopen set `D(e)` when `S = R ⧸ (1 - e)`, then the base change of `L ^ f` to `S`
is the `n`-th power of the base change of `L`. -/
theorem mapRingHom_smul_of_forall_eq (ψ : R →+* S) {f : LocallyConstant (PrimeSpectrum R) ℤ}
    {n : ℤ} (hf : ∀ p : PrimeSpectrum S, f (comap ψ p) = n) (L : Pic R) :
    mapRingHom ψ (f • Additive.ofMul L).toMul = mapRingHom ψ L ^ n := by
  have h := mapRingHom_smul ψ f (.ofMul L)
  simp only [show f.comap ⟨comap ψ, continuous_comap ψ⟩ = .const _ n from LocallyConstant.ext hf,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, const_smul_ofMul] at h
  simpa using congr_arg Additive.toMul h

end CommRing.Pic
