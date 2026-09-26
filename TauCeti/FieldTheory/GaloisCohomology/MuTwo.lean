module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# The `μ₂` coefficients as trivial `F₂` coefficients

Let `K` be a field with `[Invertible (2 : K)]` and `G_K = AbsoluteGaloisGroup K`. This file
identifies the Kummer coefficient module `μ₂ = μ₂(Kˢ)` of `TauCeti.Kummer` with the trivial `𝔽₂`
coefficient object `TauCeti.trivialF2 G_K` of the profinite-cohomology layer.

The identification is elementary: an element of `μ₂` is a root of unity `ζ` of a separable closure
with `ζ ^ 2 = 1`, so `ζ` is `±1`, and `±1 ∈ K`, so the Galois action on `μ₂` is trivial
(`TauCeti.kummerCoeff_smul_eq_self`). The value dictionary `TauCeti.mu2EquivZMod2` sends `0` to
`0` and `-1` to `1`; its type pins it, because the only nontrivial additive self-equivalence of
`ZMod 2` is the identity, and `-1` is the nontrivial element of `μ₂` as soon as `2` is invertible
in `K`.

Crossed with the universe lift of `TauCeti.trivialF2Equiv` and read in the category
`TopRep ℤ G_K`, this is the isomorphism of coefficient objects
`TauCeti.kummerCoeffIsoTrivialF2`, the only coefficient transport used at `n = 2`. Nothing here is
specific to local fields: it holds for every field in which `2` is invertible, and it fails
precisely where the action on `μ₂` is not trivial.

## Main definitions

* `TauCeti.negOne`: the nontrivial element of `μ₂`, that is `-1` read as a `2`nd root of unity.
* `TauCeti.mu2EquivZMod2`: the value dictionary `μ₂ ≃+ ZMod 2`.
* `TauCeti.kummerCoeffEquiv`: the same dictionary, crossed with the universe lift, as an additive
  equivalence of the coefficient carriers `KummerCoeff K 2 ≃+ (trivialF2 G_K).V`.
* `TauCeti.kummerCoeffIsoTrivialF2`: the isomorphism of coefficient objects
  `ofDiscreteModule ℤ G_K (KummerCoeff K 2) ≅ trivialF2 G_K`.
* `TauCeti.isUnit_natCast_two`: `2` is a unit of `K` in the `ℕ`-coerced spelling the Kummer
  statements are made in.
* `TauCeti.kummerClass`: the Kummer class `(a) ∈ H¹(G_K, 𝔽₂)` of a unit, read in the
  `trivialF2 G_K` carrier.

## Main results

* `TauCeti.toMul_eq_one_or_neg_one` and `TauCeti.eq_zero_or_eq_negOne`: the `2`nd roots of unity of
  a separable closure are `1` and `-1`, so an element of `μ₂` is `0` or `negOne`.
* `TauCeti.negOne_ne_zero` and `TauCeti.zero_ne_negOne`: the two elements of `μ₂` are distinct,
  because `2` is invertible in `K`.
* `TauCeti.mu2EquivZMod2_apply_zero`, `TauCeti.mu2EquivZMod2_apply_negOne`,
  `TauCeti.mu2EquivZMod2_eq_one_iff`: the value dictionary on its two values.
* `TauCeti.kummerCoeff_smul_eq_self`: the Galois action on `μ₂` is trivial.
* `TauCeti.mu2EquivZMod2_equivariant`: the value dictionary is fixed by `G_K`, which is what makes
  it a morphism of coefficient objects.
* `TauCeti.kummerClass_eq_zero_of_square`: the Kummer class of a square vanishes. The converse is
  not stated: it is the injectivity of the coefficient map on `H¹`, which Mathlib's
  `continuousCohomology` does not provide.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., §1.4, for the
  `2`nd roots of unity in a separable closure and the resulting trivial Galois action.
-/

public section

open scoped ContRepresentation

noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

variable {K : Type u} [Field K]

/-! ### The elements of `μ₂` -/

/-- The nontrivial element of `μ₂`, that is `-1` read as a `2`nd root of unity in a separable
closure of the base field. -/
noncomputable def negOne : KummerCoeff K 2 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (-1 : (SeparableClosure K)) (by simp))

@[simp]
theorem toMul_negOne : negOne.toMul.1 = (-1 : (SeparableClosure K)ˣ) :=
  Units.ext (by simp [negOne])

/-- **The `2`nd roots of unity of a separable closure are `1` and `-1`**, when `2` is invertible
in the base field: `ζ ^ 2 = 1` in a field forces `ζ = 1` or `ζ = -1`, by factoring `ζ ^ 2 - 1`.
Invertibility of `2` is what rules out characteristic two, where `-1 = 1`. -/
theorem toMul_eq_one_or_neg_one [Invertible (2 : K)] (x : KummerCoeff K 2) :
    x.toMul = 1 ∨ x.toMul.1 = -1 := by
  have hu : (x.toMul.1 : (SeparableClosure K)ˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 _).1 x.toMul.2
  have hx : (Units.val x.toMul.1 : (SeparableClosure K)) ^ 2 = 1 := congrArg Units.val hu
  have hfac : (Units.val x.toMul.1 - 1) * (Units.val x.toMul.1 + 1) = 0 := by
    rw [mul_comm, ← sq_sub_sq, hx, one_pow, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (Subtype.ext (Units.ext (by
      simpa using (sub_eq_zero (a := Units.val x.toMul.1) (b := 1)).mp h)))
  · exact Or.inr (Units.ext (by
      simpa using (eq_neg_iff_add_eq_zero (a := Units.val x.toMul.1) (b := 1)).mpr h))

/-- An element of `μ₂` is `0` or `-1`. -/
theorem eq_zero_or_eq_negOne [Invertible (2 : K)] (x : KummerCoeff K 2) :
    x = 0 ∨ x = negOne := by
  rcases toMul_eq_one_or_neg_one x with h | h
  · exact Or.inl (Additive.toMul.injective h)
  · exact Or.inr (Additive.toMul.injective (Subtype.ext (h.trans toMul_negOne.symm)))

/-- The two elements of `μ₂` are distinct, because `2` is invertible in the base field. -/
theorem negOne_ne_zero [Invertible (2 : K)] : negOne ≠ (0 : KummerCoeff K 2) := by
  intro h
  have h1 : (-1 : (SeparableClosure K)ˣ) = 1 := by
    simpa using congrArg Subtype.val (congrArg Additive.toMul h)
  have h' : (-1 : (SeparableClosure K)) = 1 := by
    simpa using congrArg Units.val h1
  have hz : (2 : (SeparableClosure K)) = 0 := by
    rw [show (2 : (SeparableClosure K)) = 1 + 1 by norm_num,
      show (1 : (SeparableClosure K)) + 1 = 0 from
        (congrArg (fun z : (SeparableClosure K) => z + 1) h'.symm).trans (neg_add_cancel 1)]
  exact (map_ne_zero (algebraMap K (SeparableClosure K)) (a := (2 : K))).mpr
    (Invertible.ne_zero (2 : K)) hz

theorem zero_ne_negOne [Invertible (2 : K)] : (0 : KummerCoeff K 2) ≠ negOne :=
  negOne_ne_zero.symm

private theorem negOne_add_negOne : (negOne : KummerCoeff K 2) + negOne = 0 := by
  refine Additive.toMul.injective (Subtype.ext (Units.ext (by simp)))

/-! ### The trivial Galois action -/

variable (K) [Invertible (2 : K)]

/-- **The Galois action on `μ₂` is trivial.** Every `2`nd root of unity in a separable closure is
`±1` (TauCeti.toMul_eq_one_or_neg_one), hence lies in the base field and is fixed by `G_K`. This
is what makes the Kummer coefficients at `n = 2` isomorphic to the trivial `F₂` coefficient
object, and it is false at `n > 2`, which is why every mod-2 statement carries
`[Invertible (2 : K)]` rather than a general `n`. -/
theorem kummerCoeff_smul_eq_self (g : AbsoluteGaloisGroup K) (x : KummerCoeff K 2) :
    g • x = x := by
  refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
  rcases toMul_eq_one_or_neg_one x with h | h <;> simp [h]

/-! ### The value dictionary -/

/-- **`2` is a unit of `K`**, in the `ℕ`-coerced spelling the Kummer statements are made in: the
Kummer isomorphism and the map `H²(G_K, μ₂) → H²(G_K, (Kˢ)ˣ)` both ask for `IsUnit (2 : K)`. -/
theorem isUnit_natCast_two : IsUnit ((2 : ℕ) : K) := by
  simpa using isUnit_of_invertible (2 : K)

/-- `μ₂` has decidable equality, through the two elements `TauCeti.eq_zero_or_eq_negOne` names. -/
noncomputable local instance decidableEqMu2 (x y : KummerCoeff K 2) : Decidable (x = y) :=
  Classical.propDecidable (x = y)

/-- **The `μ₂` coefficient module is `ZMod 2`**, as an additive group, with `0` sent to `0` and
`-1` to `1`. There is only one additive equivalence `ZMod 2 ≃+ ZMod 2`, so the choice of generator
is the whole content, and it is canonical: the generator is the nontrivial element `-1` of `μ₂`. -/
noncomputable def mu2EquivZMod2 : KummerCoeff K 2 ≃+ ZMod 2 where
  toFun x := if x = negOne then 1 else 0
  invFun b := if b = 1 then negOne else 0
  left_inv x := by
    rcases eq_zero_or_eq_negOne x with hx | hx
    · simp only [hx, ite_eq_right zero_ne_negOne, ite_eq_right (by decide : ¬((0 : ZMod 2) = 1))]
    · simp only [hx, ite_true]
  right_inv b := by
    by_cases hb : b = 0
    · simp only [hb, ite_eq_right (by decide : ¬((0 : ZMod 2) = 1)), ite_eq_right zero_ne_negOne]
    · have hlt : b.val < 2 := ZMod.val_lt b
      have hne : b.val ≠ 0 := (ZMod.val_ne_zero b).2 hb
      have hval : b.val = 1 := by omega
      have hb1 : b = 1 := by
        rw [← ZMod.natCast_zmod_val b, hval]
        norm_num
      simp only [hb1, ite_true]
  map_add' x y := by
    rcases eq_zero_or_eq_negOne x with hx | hx
    · rcases eq_zero_or_eq_negOne y with hy | hy
      · simp only [hx, hy, add_zero, ite_eq_right zero_ne_negOne]
      · simp only [hx, hy, ite_eq_right zero_ne_negOne, zero_add]
    · rcases eq_zero_or_eq_negOne y with hy | hy
      · simp only [hx, hy, add_zero, ite_true, ite_eq_right zero_ne_negOne]
      · simp only [hx, hy, negOne_add_negOne, ite_true, ite_eq_right zero_ne_negOne]
        decide

@[simp]
theorem mu2EquivZMod2_apply_zero : mu2EquivZMod2 K 0 = 0 := by
  change (if (0 : KummerCoeff K 2) = negOne then 1 else 0 : ZMod 2) = 0
  rw [ite_eq_right zero_ne_negOne]

@[simp]
theorem mu2EquivZMod2_apply_negOne : mu2EquivZMod2 K negOne = 1 := by
  change (if (negOne : KummerCoeff K 2) = negOne then 1 else 0 : ZMod 2) = 1
  rw [ite_eq_left rfl]

theorem mu2EquivZMod2_eq_one_iff (x : KummerCoeff K 2) :
    mu2EquivZMod2 K x = 1 ↔ x = negOne := by
  constructor
  · intro hx
    rcases eq_zero_or_eq_negOne x with h | h
    · rw [h, mu2EquivZMod2_apply_zero] at hx
      exact absurd hx (by decide)
    · exact h
  · intro hx
    rw [hx, mu2EquivZMod2_apply_negOne]

/-- The `μ₂` coefficient identification is equivariant: the Galois action on `μ₂` is trivial, so
the value dictionary is fixed by `G_K`. This is what makes the Kummer coefficients at `n = 2`
isomorphic to a trivial coefficient object. -/
theorem mu2EquivZMod2_equivariant (g : AbsoluteGaloisGroup K) (x : KummerCoeff K 2) :
    mu2EquivZMod2 K (g • x) = mu2EquivZMod2 K x :=
  congrArg (mu2EquivZMod2 K) (kummerCoeff_smul_eq_self K g x)

/-! ### The coefficient object -/

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The coefficient carriers of `μ₂` and of the trivial `𝔽₂` object are the same additive
group.** This is `TauCeti.mu2EquivZMod2` crossed with the universe lift of
`TauCeti.trivialF2Equiv`; it is the dictionary read on carriers, and
`TauCeti.kummerCoeffIsoTrivialF2` is the same dictionary read in the category `TopRep ℤ G_K`. -/
noncomputable def kummerCoeffEquiv :
    KummerCoeff K 2 ≃+ (trivialF2 (AbsoluteGaloisGroup K)).V :=
  (mu2EquivZMod2 K).trans (trivialF2Equiv (AbsoluteGaloisGroup K)).symm

/-- The dictionary is the value dictionary crossed with the universe lift. -/
@[simp]
theorem kummerCoeffEquiv_apply (x : KummerCoeff K 2) :
    kummerCoeffEquiv K x = (trivialF2Equiv (AbsoluteGaloisGroup K)).symm (mu2EquivZMod2 K x) := by
  rw [kummerCoeffEquiv, AddEquiv.trans_apply]

/-- The inverse dictionary reads a value through the universe lift. -/
@[simp]
theorem kummerCoeffEquiv_symm_apply (b : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    (kummerCoeffEquiv K).symm b =
      (mu2EquivZMod2 K).symm (trivialF2Equiv (AbsoluteGaloisGroup K) b) := by
  rw [kummerCoeffEquiv, AddEquiv.symm_trans_apply]
  have hsymm : (trivialF2Equiv (AbsoluteGaloisGroup K)).symm.symm b
      = trivialF2Equiv (AbsoluteGaloisGroup K) b :=
    Equiv.symm_symm_apply (trivialF2Equiv (AbsoluteGaloisGroup K)).toEquiv b
  rw [hsymm]

/-- The dictionary is `G_K`-equivariant, the two sides being the trivial action. -/
private theorem kummerCoeffEquiv_equivariant (g : AbsoluteGaloisGroup K) (x : KummerCoeff K 2) :
    kummerCoeffEquiv K (g • x) = g • kummerCoeffEquiv K x := by
  simp only [kummerCoeffEquiv_apply, mu2EquivZMod2_equivariant,
    TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]

private noncomputable def kummerCoeffToTrivialF2 :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2) ⟶
      ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V :=
  ofDiscreteModuleMap (kummerCoeffEquiv K).toIntLinearEquiv (kummerCoeffEquiv_equivariant K)

private noncomputable def kummerCoeffFromTrivialF2 :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V ⟶
      ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2) :=
  ofDiscreteModuleMap (kummerCoeffEquiv K).symm.toIntLinearEquiv (fun g b => by
    change (kummerCoeffEquiv K).symm (g • b) = g • (kummerCoeffEquiv K).symm b
    simp only [kummerCoeffEquiv_symm_apply, TopRep.distribMulAction_smul,
      trivialF2_ρ_apply_apply, kummerCoeff_smul_eq_self K g])

/-- **The Kummer coefficients at `n = 2` and the trivial `𝔽₂` coefficient object are the same
coefficient object.** The isomorphism is the value dictionary of `TauCeti.mu2EquivZMod2`, crossed
with the universe lift of `TauCeti.trivialF2Equiv`, and it is a morphism of coefficient objects
because the Galois action on `μ₂` is trivial (`TauCeti.kummerCoeff_smul_eq_self`). This is the
only coefficient transport used at `n = 2`. -/
noncomputable def kummerCoeffIsoTrivialF2 :
    ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K 2) ≅
      trivialF2 (AbsoluteGaloisGroup K) := by
  rw [← ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)]
  exact
    { hom := kummerCoeffToTrivialF2 K
      inv := kummerCoeffFromTrivialF2 K
      hom_inv_id := by
        refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : KummerCoeff K 2) => ?_)
        change (kummerCoeffFromTrivialF2 K) ((kummerCoeffToTrivialF2 K) m) = m
        have hout : (kummerCoeffFromTrivialF2 K) ((kummerCoeffToTrivialF2 K) m)
            = (kummerCoeffEquiv K).symm ((kummerCoeffEquiv K) m) := by
          have hto : (kummerCoeffToTrivialF2 K) m = (kummerCoeffEquiv K) m :=
            ofDiscreteModuleMap_hom_apply _ _ _
          rw [hto]
          exact ofDiscreteModuleMap_hom_apply _ _ _
        rw [hout, AddEquiv.symm_apply_apply]
      inv_hom_id := by
        refine TopRep.hom_ext
          (DFunLike.ext _ _ fun (b : (trivialF2 (AbsoluteGaloisGroup K)).V) => ?_)
        change (kummerCoeffToTrivialF2 K) ((kummerCoeffFromTrivialF2 K) b) = b
        have hout : (kummerCoeffToTrivialF2 K) ((kummerCoeffFromTrivialF2 K) b)
            = (kummerCoeffEquiv K) ((kummerCoeffEquiv K).symm b) := by
          have hfrom : (kummerCoeffFromTrivialF2 K) b = (kummerCoeffEquiv K).symm b :=
            ofDiscreteModuleMap_hom_apply _ _ _
          rw [hfrom]
          exact ofDiscreteModuleMap_hom_apply _ _ _
        rw [hout, AddEquiv.apply_symm_apply] }

/-! ### The Kummer class of a unit -/

variable {K}

/-- **The Kummer class** `(a) ∈ H¹(G_K, 𝔽₂)` of a unit `a`. It is the supplier's
`TauCeti.kummerMapCanonical` at `n = 2`, read through the coefficient-object isomorphism
`TauCeti.kummerCoeffIsoTrivialF2`, and not a second Kummer cocycle: the body is a real term, so the
two cannot drift. -/
noncomputable def kummerClass (a : Kˣ) :
    continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  (ContinuousCohomology.coeffMap (kummerCoeffIsoTrivialF2 K).hom 1).hom
    (Multiplicative.toAdd (kummerMapCanonical K 2 (isUnit_natCast_two K) a))

variable (K)

/-- **The Kummer class of a square vanishes.** A member of `Subgroup.square Kˣ` is a square, hence
a two-th power, so `TauCeti.kummerMap_eq_one_iff` at `n = 2` makes the Kummer map trivial on it, and
the degree-one comparison `TauCeti.explicitIso_kummerMap` carries that to the Kummer class.
⚠ Only this direction is stated. The converse, that a unit with trivial Kummer class is a square,
is the statement that the coefficient map on `H¹` is injective, and that injectivity is not
available at the coefficient level today: the `hom` of a morphism of `continuousCohomology` is a
`ContinuousLinearMap`, not an `Embedding`, so `TauCeti.h2KummerToUnits_injective` had to be proved
by hand for the degree-two Kummer map, and the same hand proof is needed here. -/
theorem kummerClass_eq_zero_of_square {a : Kˣ} (ha : a ∈ Subgroup.square Kˣ) :
    kummerClass a = 0 := by
  obtain ⟨r, hr⟩ := Subgroup.mem_square.mp ha
  have hone : kummerMap K 2 (isUnit_natCast_two K) a = 1 :=
    (kummerMap_eq_one_iff (isUnit_natCast_two K) a).mpr
      ⟨r, by rw [hr, pow_two]⟩
  have hzero : Multiplicative.toAdd (kummerMapCanonical K 2 (isUnit_natCast_two K) a) = 0 := by
    rw [explicitIso_kummerMap K 2 (isUnit_natCast_two K) a, hone]
    simp
  rw [kummerClass, hzero]
  simp


end TauCeti
