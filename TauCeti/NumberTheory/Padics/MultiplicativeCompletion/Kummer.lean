/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Basic

/-!
# The limit Kummer map `lim_m Kˣ/(Kˣ)^(p^m) ≃ lim_m H¹(G_K, μ_{p^m})`

Let `K` be a field in which the natural number `p` is invertible, and `G_K` its absolute Galois
group. For each `m` the Kummer isomorphism `Kˣ ⧸ (Kˣ)^(p^m) ≃ H¹(G_K, μ_{p^m})`
(`TauCeti.kummerIso`) identifies the power classes of `K` with the first Galois cohomology of the
`p^m`-th roots of unity. As `m` varies these isomorphisms commute with the transition maps: on
power classes the transition is reduction from level `m + 1` to level `m`, and on cohomology it is
induced by the power map `μ_{p^(m+1)} → μ_{p^m}`, `ζ ↦ ζ ^ p` (`TauCeti.kummerCoeffPow`). This
file passes the Kummer isomorphisms to the inverse limit.

The source is the `p`-adic completion `A(K) = lim_m Kˣ/(Kˣ)^(p^m)` of the multiplicative group
(`TauCeti.padicCompletionUnits`). The target `TauCeti.kummerH1Limit` is the inverse limit
`lim_m H¹(G_K, μ_{p^m})` along the power maps, realized as the subgroup of compatible families in
the product of the cohomology groups. The **limit Kummer map** `TauCeti.padicKummerMap` is the
Kummer class map in every coordinate; it is injective and surjective because every finite-level
Kummer map is, and the two transition maps correspond. No finiteness of the power-class groups is
assumed, and the source is the completion of `Kˣ`, not the algebraic tensor product
`Kˣ ⊗ ℤ_p`.

For `p` prime, both sides are `ℤ_p`-modules: on `A(K)` this is
`TauCeti.padicCompletionUnitsPadicModule`, and on `lim_m H¹(G_K, μ_{p^m})` a `p`-adic integer
acts at level `m` through its residue modulo `p^m`, which is well defined since `p^m` kills
`H¹(G_K, μ_{p^m})`. The limit Kummer map is `ℤ_p`-linear, so it is a `ℤ_p`-linear isomorphism
`TauCeti.padicKummerEquiv`.

This is the algebraic part of the `p`-adic Kummer identification
`H¹(G_K, ℤ_p(1)) ≃ lim_m Kˣ/(Kˣ)^(p^m)`: what remains there is the passage from continuous
cohomology of `ℤ_p(1) = lim_m μ_{p^m}` to the inverse limit of the finite-level groups.

## Main definitions

* `TauCeti.kummerH1Transition`: the transition `H¹(G_K, μ_{p^(m+1)}) → H¹(G_K, μ_{p^m})` induced
  by the power map on roots of unity.
* `TauCeti.kummerH1Limit`: the inverse limit `lim_m H¹(G_K, μ_{p^m})`, with its intrinsic
  `ℤ_p`-module structure `TauCeti.kummerH1LimitPadicModule` for `p` prime.
* `TauCeti.kummerH1LimitLift`: the homomorphism into `lim_m H¹(G_K, μ_{p^m})` induced by a
  family of homomorphisms compatible with the transition maps.
* `TauCeti.padicKummerMap`: the limit Kummer map `A(K) → lim_m H¹(G_K, μ_{p^m})`.
* `TauCeti.padicKummerEquiv`: the limit Kummer map as a `ℤ_p`-linear isomorphism.

## Main results

* `TauCeti.kummerH1Transition_kummerMap`: the transition maps change the level of Kummer
  classes.
* `TauCeti.padicKummerMap_apply_of_eq`: the coordinates of the limit Kummer map are Kummer
  classes.
* `TauCeti.padicKummerMap_injective`, `TauCeti.padicKummerMap_surjective`: the limit Kummer map
  is bijective.
* `TauCeti.padicKummerMap_smul`: the limit Kummer map is `ℤ_p`-linear.

## References

* K. Rubin, *Euler Systems*, Chapter I, §2, Example 2.1, and Appendix B, Proposition B.2.3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

variable (p : ℕ) (K : Type*) [Field K]

/-! ### The inverse system `H¹(G_K, μ_{p^m})` -/

/-- **The transition map** `H¹(G_K, μ_{p^(m+1)}) → H¹(G_K, μ_{p^m})`, induced by the power map
`μ_{p^(m+1)} → μ_{p^m}`, `ζ ↦ ζ ^ p`, on coefficients. On Kummer classes it is the change of level
(`TauCeti.kummerH1Transition_kummerMap`). -/
def kummerH1Transition (m : ℕ) :
    H1 (AbsoluteGaloisGroup K) (KummerCoeff K (p ^ (m + 1))) →+
      H1 (AbsoluteGaloisGroup K) (KummerCoeff K (p ^ m)) :=
  explicitCoeff1 (AbsoluteGaloisGroup K) (KummerCoeff K (p ^ (m + 1)))
    (kummerCoeffPow K (pow_dvd_pow p m.le_succ)) continuous_of_discreteTopology

/-- **The inverse limit** `lim_m H¹(G_K, μ_{p^m})` along the transition maps
`TauCeti.kummerH1Transition`, realized as the subgroup of compatible families in the product of
the cohomology groups. -/
def kummerH1Limit :
    AddSubgroup (∀ m : ℕ, H1 (AbsoluteGaloisGroup K) (KummerCoeff K (p ^ m))) :=
  ⨅ m : ℕ, AddMonoidHom.eqLocus
    ((kummerH1Transition p K m).comp (Pi.evalAddMonoidHom _ (m + 1)))
    (Pi.evalAddMonoidHom _ m)

/-- A family of classes lies in the inverse limit exactly when it satisfies the transition
equation at every level. -/
@[simp]
theorem mem_kummerH1Limit_iff (y : ∀ m : ℕ, H1 (AbsoluteGaloisGroup K) (KummerCoeff K (p ^ m))) :
    y ∈ kummerH1Limit p K ↔ ∀ m, kummerH1Transition p K m (y (m + 1)) = y m := by
  rw [kummerH1Limit, AddSubgroup.mem_iInf]
  -- Membership in an equalizer `AddMonoidHom.eqLocus f g` is the equation `f y = g y` by
  -- definition; Mathlib states no membership lemma for it.
  rfl

/-- Two elements of the inverse limit agree when all their coordinates agree. -/
@[ext]
theorem kummerH1Limit_ext {y z : kummerH1Limit p K} (h : ∀ m, y.val m = z.val m) : y = z :=
  Subtype.ext (funext h)

/-- **The universal property of the inverse limit.** A family of homomorphisms into
`H¹(G_K, μ_{p^m})` compatible with the transition maps `TauCeti.kummerH1Transition` induces a
homomorphism into `lim_m H¹(G_K, μ_{p^m})`. -/
def kummerH1LimitLift {A : Type*} [AddZeroClass A]
    (f : ∀ m : ℕ, A →+ H1 (AbsoluteGaloisGroup K) (KummerCoeff K (p ^ m)))
    (hf : ∀ m x, kummerH1Transition p K m (f (m + 1) x) = f m x) :
    A →+ kummerH1Limit p K :=
  AddMonoidHom.codRestrict (AddMonoidHom.pi f) _ fun x ↦
    (mem_kummerH1Limit_iff p K _).2 fun m ↦ hf m x

/-- The induced homomorphism is computed by the given homomorphism at every level. -/
@[simp]
theorem kummerH1LimitLift_apply {A : Type*} [AddZeroClass A]
    (f : ∀ m : ℕ, A →+ H1 (AbsoluteGaloisGroup K) (KummerCoeff K (p ^ m)))
    (hf : ∀ m x, kummerH1Transition p K m (f (m + 1) x) = f m x) (x : A) (m : ℕ) :
    (kummerH1LimitLift p K f hf x).val m = f m x := by
  simp [kummerH1LimitLift]

variable {p K}

/-- The transition map sends the Kummer class of a unit at level `m + 1` to its Kummer class at
level `m`. -/
theorem kummerH1Transition_kummerMap (hp : IsUnit (p : K)) (m : ℕ) (a : Kˣ) :
    kummerH1Transition p K m
        (Multiplicative.toAdd
          (kummerMap K (p ^ (m + 1)) (Nat.cast_pow (α := K) p (m + 1) ▸ hp.pow (m + 1)) a)) =
      Multiplicative.toAdd (kummerMap K (p ^ m) (Nat.cast_pow (α := K) p m ▸ hp.pow m) a) :=
  explicitCoeff1_kummerCoeffPow_kummerMap _ _ a

/-! ### The limit Kummer map -/

/-- The Kummer isomorphism `TauCeti.kummerIso` at level `p^m` on the coordinate
`Kˣ ⧸ (Kˣ)^(p^m)` of `A(K)`, whose denominator is spelled as the range of the power map rather
than as `TauCeti.powerSubgroup`. -/
private def kummerCoord (hp : IsUnit (p : K)) (m : ℕ) :
    (Kˣ ⧸ (powMonoidHom (p ^ m) : Kˣ →* Kˣ).range) ≃*
      Multiplicative (H1 (AbsoluteGaloisGroup K) (KummerCoeff K (p ^ m))) :=
  (QuotientGroup.quotientMulEquivOfEq
      (powerSubgroup_eq_range_powMonoidHom Kˣ (p ^ m)).symm).trans
    (kummerIso K (p ^ m) (Nat.cast_pow (α := K) p m ▸ hp.pow m))

private theorem kummerCoord_mk (hp : IsUnit (p : K)) (m : ℕ) (a : Kˣ) :
    kummerCoord hp m (a : Kˣ ⧸ (powMonoidHom (p ^ m) : Kˣ →* Kˣ).range) =
      kummerMap K (p ^ m) (Nat.cast_pow (α := K) p m ▸ hp.pow m) a := by
  rw [kummerCoord, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk, kummerIso_mk]

/-- The Kummer class maps commute with the transition maps of the two inverse systems. -/
private theorem kummerH1Transition_kummerCoord (hp : IsUnit (p : K)) (m : ℕ)
    (x : Kˣ ⧸ (powMonoidHom (p ^ (m + 1)) : Kˣ →* Kˣ).range) :
    kummerH1Transition p K m (Multiplicative.toAdd (kummerCoord hp (m + 1) x)) =
      Multiplicative.toAdd (kummerCoord hp m (padicCompletionTransition p K m x)) := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [kummerCoord_mk, padicCompletionTransition_mk, kummerCoord_mk]
    exact kummerH1Transition_kummerMap hp m a

variable (p K)

/-- **The limit Kummer map** `A(K) = lim_m Kˣ/(Kˣ)^(p^m) → lim_m H¹(G_K, μ_{p^m})`, for `p`
invertible in `K`: the Kummer class map `TauCeti.kummerClassMap` in every coordinate
(`TauCeti.padicKummerMap_apply_of_eq`). It is bijective (`TauCeti.padicKummerMap_injective`,
`TauCeti.padicKummerMap_surjective`). -/
def padicKummerMap (hp : IsUnit (p : K)) :
    Additive (padicCompletionUnits p K) →+ kummerH1Limit p K where
  toFun x := ⟨fun m ↦ Multiplicative.toAdd (kummerCoord hp m (x.toMul.val m)), by
    rw [mem_kummerH1Limit_iff]
    intro m
    rw [kummerH1Transition_kummerCoord hp m,
      (mem_padicCompletionUnits_iff p K x.toMul.val).1 x.toMul.property m]⟩
  map_zero' := by
    ext m
    exact congrArg Multiplicative.toAdd (map_one (kummerCoord hp m))
  map_add' x y := by
    ext m
    exact congrArg Multiplicative.toAdd (map_mul (kummerCoord hp m) _ _)

variable {p K}

private theorem padicKummerMap_apply (hp : IsUnit (p : K))
    (x : Additive (padicCompletionUnits p K)) (m : ℕ) :
    (padicKummerMap p K hp x).val m = Multiplicative.toAdd (kummerCoord hp m (x.toMul.val m)) :=
  (rfl)

/-- **The coordinates of the limit Kummer map.** If the `m`-th coordinate of `x ∈ A(K)` is the
power class of `a ∈ Kˣ`, the `m`-th coordinate of its image is the Kummer class of `a` in
`H¹(G_K, μ_{p^m})`. -/
theorem padicKummerMap_apply_of_eq (hp : IsUnit (p : K))
    {x : Additive (padicCompletionUnits p K)} {m : ℕ} {a : Kˣ} (h : x.toMul.val m = a) :
    (padicKummerMap p K hp x).val m =
      Multiplicative.toAdd (kummerMap K (p ^ m) (Nat.cast_pow (α := K) p m ▸ hp.pow m) a) := by
  rw [padicKummerMap_apply, h, kummerCoord_mk]

/-- The limit Kummer map sends the class of a unit `a ∈ Kˣ` in `A(K)` to the family of its Kummer
classes in `H¹(G_K, μ_{p^m})`. -/
@[simp]
theorem padicKummerMap_padicCompletionUnitsOf (hp : IsUnit (p : K)) (a : Kˣ) (m : ℕ) :
    (padicKummerMap p K hp (Additive.ofMul (padicCompletionUnitsOf p K a))).val m =
      Multiplicative.toAdd (kummerMap K (p ^ m) (Nat.cast_pow (α := K) p m ▸ hp.pow m) a) :=
  padicKummerMap_apply_of_eq hp (by
    rw [toMul_ofMul, padicCompletionUnitsOf_apply, QuotientGroup.mk'_apply])

/-- **The limit Kummer map is injective.** -/
theorem padicKummerMap_injective (hp : IsUnit (p : K)) :
    Function.Injective (padicKummerMap p K hp) := fun x y h ↦ by
  refine Additive.toMul.injective (Subtype.ext (funext fun m ↦ ?_))
  have hm := congrArg (fun z ↦ z.val m) h
  rw [padicKummerMap_apply, padicKummerMap_apply] at hm
  exact (kummerCoord hp m).injective (Multiplicative.toAdd.injective hm)

/-- **The limit Kummer map is surjective.** -/
theorem padicKummerMap_surjective (hp : IsUnit (p : K)) :
    Function.Surjective (padicKummerMap p K hp) := by
  intro y
  -- Take preimages of the coordinates under the Kummer isomorphisms; they form a compatible
  -- family because the Kummer isomorphisms commute with the transition maps and are injective.
  choose x hx using fun m ↦ (kummerCoord hp m).surjective (Multiplicative.ofAdd (y.val m))
  have hcompat : x ∈ padicCompletionUnits p K := by
    rw [mem_padicCompletionUnits_iff]
    intro m
    refine (kummerCoord hp m).injective (Multiplicative.toAdd.injective ?_)
    rw [← kummerH1Transition_kummerCoord hp m, hx, hx, toAdd_ofAdd, toAdd_ofAdd]
    exact (mem_kummerH1Limit_iff p K y.val).1 y.property m
  refine ⟨Additive.ofMul ⟨x, hcompat⟩, ?_⟩
  ext m
  rw [padicKummerMap_apply, toMul_ofMul]
  exact congrArg Multiplicative.toAdd (hx m)

/-- **The limit Kummer map is bijective.** -/
theorem padicKummerMap_bijective (hp : IsUnit (p : K)) :
    Function.Bijective (padicKummerMap p K hp) :=
  ⟨padicKummerMap_injective hp, padicKummerMap_surjective hp⟩

/-! ### The `ℤ_p`-module structure -/

section PadicModule

variable [Fact p.Prime]

variable (p K)

/-- A `p`-adic integer acts on `lim_m H¹(G_K, μ_{p^m})` through its residue modulo `p^m` at
level `m`. -/
instance kummerH1LimitSMul : SMul ℤ_[p] (kummerH1Limit p K) where
  smul a y := ⟨fun m ↦ a.appr m • y.val m, by
    rw [mem_kummerH1Limit_iff]
    intro m
    rw [map_nsmul, (mem_kummerH1Limit_iff p K y.val).1 y.property m]
    exact nsmul_eq_nsmul_of_modEq (a.appr_modEq m.le_succ) (nsmul_H1_kummerCoeff_eq_zero _)⟩

variable {p K}

/-- Scalar multiplication on the inverse limit is multiplication by the residue modulo `p^m` in
the `m`-th coordinate. -/
@[simp]
theorem kummerH1Limit_smul_apply (a : ℤ_[p]) (y : kummerH1Limit p K) (m : ℕ) :
    (a • y).val m = a.appr m • y.val m :=
  (rfl)

variable (p K)

/-- **The intrinsic `ℤ_p`-module structure on `lim_m H¹(G_K, μ_{p^m})`.** -/
instance kummerH1LimitPadicModule : Module ℤ_[p] (kummerH1Limit p K) where
  one_smul y := by
    ext m
    simpa using nsmul_eq_nsmul_of_modEq (PadicInt.appr_natCast_modEq 1 m)
      (nsmul_H1_kummerCoeff_eq_zero (y.val m))
  mul_smul a b y := by
    ext m
    simp only [kummerH1Limit_smul_apply]
    rw [smul_smul]
    exact nsmul_eq_nsmul_of_modEq (PadicInt.appr_mul_modEq a b m)
      (nsmul_H1_kummerCoeff_eq_zero _)
  smul_zero a := by
    ext m
    simp
  smul_add a y z := by
    ext m
    simp only [kummerH1Limit_smul_apply, AddSubgroup.coe_add, Pi.add_apply]
    exact nsmul_add _ _ _
  add_smul a b y := by
    ext m
    simp only [kummerH1Limit_smul_apply, AddSubgroup.coe_add, Pi.add_apply]
    rw [← add_nsmul]
    exact nsmul_eq_nsmul_of_modEq (PadicInt.appr_add_modEq a b m)
      (nsmul_H1_kummerCoeff_eq_zero _)
  zero_smul y := by
    ext m
    simpa using nsmul_eq_nsmul_of_modEq (PadicInt.appr_natCast_modEq 0 m)
      (nsmul_H1_kummerCoeff_eq_zero (y.val m))

variable {p K}

/-- **The limit Kummer map is `ℤ_p`-linear.** -/
theorem padicKummerMap_smul (hp : IsUnit (p : K)) (a : ℤ_[p])
    (x : Additive (padicCompletionUnits p K)) :
    padicKummerMap p K hp (a • x) = a • padicKummerMap p K hp x := by
  ext m
  rw [padicKummerMap_apply, kummerH1Limit_smul_apply, padicKummerMap_apply,
    padicCompletionUnits_smul_apply, map_pow, toAdd_pow]

variable (p K)

/-- **The limit Kummer isomorphism** `lim_m Kˣ/(Kˣ)^(p^m) ≃ lim_m H¹(G_K, μ_{p^m})` of
`ℤ_p`-modules, for a prime `p` invertible in `K`. -/
def padicKummerEquiv (hp : IsUnit (p : K)) :
    Additive (padicCompletionUnits p K) ≃ₗ[ℤ_[p]] kummerH1Limit p K :=
  LinearEquiv.ofBijective
    { toFun := padicKummerMap p K hp
      map_add' := map_add _
      map_smul' := padicKummerMap_smul hp }
    (padicKummerMap_bijective hp)

variable {p K}

/-- The limit Kummer isomorphism is the limit Kummer map. -/
@[simp]
theorem padicKummerEquiv_apply (hp : IsUnit (p : K)) (x : Additive (padicCompletionUnits p K)) :
    padicKummerEquiv p K hp x = padicKummerMap p K hp x :=
  (rfl)

end PadicModule

end TauCeti
