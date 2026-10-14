/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.CharacterCarry
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.ProductFormula
import TauCeti.NumberTheory.Cyclotomic.PrimePower
import TauCeti.Algebra.AddCircle
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Map
import TauCeti.FieldTheory.Galois.FixedField

/-!
# Reciprocity and Brauer invariants in composita of cyclotomic towers

The cyclotomic product formula at each prime implies reciprocity on every normal subextension
of a finite compositum of prime-power cyclotomic towers. In particular, the local invariants
of a Brauer class split by a cyclic subextension of such a compositum sum to zero. This allows
the splitting extension to involve several primes, rather than requiring it to lie in a
single prime-power tower. The theorem
`sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_adjoin_nth_roots` gives the result for
every cyclic subextension of `K(μ_m)/K`, for any nonzero conductor `m`.

The simultaneous cyclotomic characters have values in a finite product of groups of p-adic
units. Their common kernel fixes the compositum. A character of its Galois group therefore
factors through the image of this product map. Finiteness of the family is essential when
choosing a common finite support for the local factors.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Lemmas 8.4 and 8.5.
* J. Tate, *Global class field theory*, in Cassels–Fröhlich, *Algebraic Number Theory*,
  Chapter VII, §11.

The prime-by-prime product formula and the cyclic-class comparison are supplied by
`Global.Cyclotomic.ProductFormula` and `Global.CharacterCarry`, respectively.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField _root_.IntermediateField

variable {ι : Type*} [Finite ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
  {K : Type} [Field K] [NumberField K] (E : IntermediateField K (SeparableClosure K))

/-- The local Artin symbols of a nonzero global element satisfy reciprocity on every normal
subextension of a finite compositum of prime-power cyclotomic towers, after applying any
additive character of its Galois group. -/
theorem finsum_add_sum_apply_restrictNormalHom_eq_zero_of_le_iSup_adjoin
    [Normal K E]
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
    (σ : ∀ v : HeightOneSpectrum (𝓞 K), Field.absoluteGaloisGroup (v.adicCompletion K))
    (σ' : ∀ w : InfinitePlace K, Field.absoluteGaloisGroup w.Completion)
    (hE : E ≤ ⨆ i, adjoin K {ζ : SeparableClosure K | ∃ n : ℕ, ζ ^ p i ^ n = 1})
    {M : Type*} [AddCommGroup M] (χ : Additive Gal(E/K) →+ M) (a : Kˣ)
    (hσ : ∀ v, (σ v : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a))
    (hσ' : ∀ w, (σ' w : Field.absoluteGaloisGroupAbelianization w.Completion) =
      infiniteArtinAt w (Units.map (algebraMap K w.Completion) a)) :
    ∑ᶠ v, χ (.ofMul (AlgEquiv.restrictNormalHom E (absoluteGaloisGroupMap (τ v)
        (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v))))) +
      ∑ w, χ (.ofMul (AlgEquiv.restrictNormalHom E (absoluteGaloisGroupMap (τ' w)
        (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w))))) = 0 := by
  classical
  let := Fintype.ofFinite ι
  let c : Additive (AbsoluteGaloisGroup K) →+ (∀ i, Additive ℤ_[p i]ˣ) :=
    AddMonoidHom.pi fun i ↦
      (((cyclotomicCharacter (SeparableClosure K) (p i)).comp
        (MulSemiringAction.toRingAut (AbsoluteGaloisGroup K) (SeparableClosure K))).toAdditive)
  have hc (g : AbsoluteGaloisGroup K) (i : ι) :
      c (.ofMul g) i = .ofMul (cyclotomicCharacter (SeparableClosure K) (p i) g.toRingEquiv) :=
    rfl
  -- The common kernel fixes each tower, and hence their compositum and `E`.
  let φ : {φ : Additive (AbsoluteGaloisGroup K) →+ M //
      c.rangeRestrict.ker ≤ φ.ker} :=
    ⟨χ.comp (AlgEquiv.restrictNormalHom E).toAdditive, fun g hg ↦ by
      induction g using Additive.rec with | ofMul g => ?_
      have hg' : c (.ofMul g) = 0 := by
        simpa only [AddMonoidHom.ker_rangeRestrict, AddMonoidHom.mem_ker] using hg
      have hgE : AlgEquiv.restrictNormalHom E g = 1 := by
        rw [← MonoidHom.mem_ker, E.restrictNormalHom_ker]
        apply fixingSubgroup_le hE
        rw [fixingSubgroup_iSup, Subgroup.mem_iInf]
        intro i
        apply (mem_fixingSubgroup_adjoin_iff_cyclotomicCharacter_eq_one (p i)).2
        have hi := congrFun hg' i
        exact Additive.ofMul.injective (by
          simpa only [hc, Pi.zero_apply, ofMul_one] using hi)
      simp [hgE]⟩
  let ψ : c.range →+ M :=
    c.rangeRestrict.liftOfSurjective c.rangeRestrict_surjective φ
  have hψ (g : AbsoluteGaloisGroup K) :
      χ (.ofMul (AlgEquiv.restrictNormalHom E g)) = ψ (c.rangeRestrict (.ofMul g)) :=
    (c.rangeRestrict.liftOfRightInverse_comp_apply _
      (Function.rightInverse_surjInv c.rangeRestrict_surjective) φ (.ofMul g)).symm
  have hloc {L : Type} [Field L] [Algebra K L]
      (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
      (σ : Field.absoluteGaloisGroup L) (i : ι) :
      (c.rangeRestrict (.ofMul (absoluteGaloisGroupMap τ
        (absoluteGaloisGroupRestrictEquiv L σ))) : ∀ i, Additive ℤ_[p i]ˣ) i =
          .ofMul (abelianizedLocalCyclotomicCharacter (p i) L σ) := by
    rw [AddMonoidHom.coe_rangeRestrict, hc, cyclotomicCharacter_absoluteGaloisGroupMap,
      cyclotomicCharacter_absoluteGaloisGroupRestrictEquiv, abelianizedLocalCyclotomicCharacter_mk]
  let f (i : ι) (v : HeightOneSpectrum (𝓞 K)) :=
    abelianizedLocalCyclotomicCharacter (p i) (v.adicCompletion K)
      (artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a))
  have hf v i := (hloc (τ v) (σ v) i).trans (congrArg _ (congrArg _ (hσ v)))
  have hf' w i := (hloc (τ' w) (σ' w) i).trans (congrArg _ (congrArg _ (hσ' w)))
  have hfin (i : ι) : (Function.mulSupport (f i)).Finite :=
    hasFiniteMulSupport_abelianizedLocalCyclotomicCharacter_artinMap (p i) a
  let s : Finset (HeightOneSpectrum (𝓞 K)) :=
    Finset.univ.biUnion fun i ↦ (hfin i).toFinset
  have hsupport (i : ι) : Function.mulSupport (f i) ⊆ s := by
    intro v hv
    simp only [s, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Set.Finite.mem_toFinset]
    exact ⟨i, hv⟩
  -- One finite set contains the support of every coordinate, so also of the character.
  rw [finsum_eq_sum_of_support_subset _ (s := s) fun v hv ↦ by
    by_contra hvs
    apply hv
    dsimp only
    rw [hψ, ← map_zero ψ]
    apply congrArg ψ
    apply Subtype.ext
    funext i
    rw [hf]
    exact congrArg Additive.ofMul
      (Function.notMem_mulSupport.1 fun h ↦ hvs (hsupport i h))]
  simp only [hψ, ← map_sum, ← map_add]
  rw [← map_zero ψ]
  refine congrArg ψ (Subtype.ext (funext fun i ↦ ?_))
  simp only [AddSubgroup.coe_add, AddSubgroup.val_finsetSum, Pi.add_apply,
    Finset.sum_apply, hf, hf', ← ofMul_prod, ← ofMul_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
  rw [← finprod_eq_prod_of_mulSupport_subset (f i) (hsupport i),
    finprod_mul_prod_abelianizedLocalCyclotomicCharacter_artinMap_eq_one, ofMul_one]

/-- The local invariants of a Brauer class split by a cyclic subextension of a finite
compositum of prime-power cyclotomic towers sum to zero. -/
theorem sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_iSup_adjoin
    [FiniteDimensional K E] [IsGalois K E] [IsCyclic Gal(E/K)]
    (hE : E ≤ ⨆ i, adjoin K {ζ : SeparableClosure K | ∃ n : ℕ, ζ ^ p i ^ n = 1})
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) Eˣ) 2) :
    sumLocalInv K (brLocalization K (relBrInfl K E E.val y)) = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(E/K))
  let e : Gal(E/K) ≃* Multiplicative (ZMod (Module.finrank K E)) :=
    (zmodMulEquivOfGenerator hg (IsGalois.card_aut_eq_finrank K E)).symm
  let χ : Additive Gal(E/K) →+ AddCircle (1 : ℚ) :=
    (ZMod.toRatAddCircle (Module.finrank K E)).comp (MulEquiv.toAdditiveLeft e).toAddMonoidHom
  have hχ : χ (.ofMul g) = ((1 / Module.finrank K E : ℚ) : AddCircle (1 : ℚ)) := by
    simpa [χ, e] using ZMod.toRatAddCircle_natCast (Module.finrank K E) 1
  have hσ (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) := QuotientGroup.mk_surjective
    (artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a))
  have hσ' (a : Kˣ) (w : InfinitePlace K) := QuotientGroup.mk_surjective
    (infiniteArtinAt w (Units.map (algebraMap K w.Completion) a))
  refine (forall_sumLocalInv_brLocalization_relBrInfl_eq_zero_iff E hg
    (fun _ ↦ IsSepClosed.lift) (fun _ ↦ IsSepClosed.lift) (fun a v ↦ (hσ a v).choose)
    (fun a w ↦ (hσ' a w).choose) hχ (fun a v ↦ (hσ a v).choose_spec)
    (fun a w ↦ (hσ' a w).choose_spec)).2 (fun a ↦ ?_) y
  exact finsum_add_sum_apply_restrictNormalHom_eq_zero_of_le_iSup_adjoin p E _ _ _ _ hE χ a
    (fun v ↦ (hσ a v).choose_spec) (fun w ↦ (hσ' a w).choose_spec)

omit [Finite ι] [∀ i, Fact (p i).Prime] in
/-- The sum of local invariants vanishes on every Brauer class split by a cyclic subextension
of `K(μ_m)/K`, for any nonzero `m`. -/
theorem sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_adjoin_nth_roots
    [FiniteDimensional K E] [IsGalois K E] [IsCyclic Gal(E/K)]
    {m : ℕ} (hm : m ≠ 0) (hE : E ≤ adjoin K {ζ : SeparableClosure K | ζ ^ m = 1})
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) Eˣ) 2) :
    sumLocalInv K (brLocalization K (relBrInfl K E E.val y)) = 0 := by
  classical
  let (q : ↥m.primeFactors) : Fact q.1.Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
  exact sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_iSup_adjoin
    (fun q : ↥m.primeFactors ↦ q.1) E
    (hE.trans (adjoin_nth_roots_le_iSup_adjoin_prime_pow hm)) y

end TauCeti.ClassFieldTheory
