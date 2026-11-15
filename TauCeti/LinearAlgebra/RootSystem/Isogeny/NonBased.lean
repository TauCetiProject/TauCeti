/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Power
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A

/-!
# Based endo-isogenies of root pairings and the non-based `A₁` reflection isogeny

An endo-isogeny `f : RootPairingIsogeny P P` of a root pairing with a chosen base `b : P.Base` is
*based* (`RootPairingIsogeny.IsBased b f`) if its index bijection preserves the positive roots
`posRoots P b`. Every positive scaling `RootPairingIsogeny.smulId P c` is based, and based
endo-isogenies are closed under composition and powers.

By contrast, on the pinned simply connected `A₁` root datum `typeASimplyConnectedRootDatum 1`, the
composite `a1ReflectionIsogeny c` of the unique reflection automorphism with `smulId _ c` has:

* weight and coweight maps equal to `-((c : ℕ) • LinearMap.id)`;
* constant exponent `c`;
* square `a1ReflectionIsogeny c * a1ReflectionIsogeny c = smulId _ (c ^ 2)` (at `c = p`, the
  root-datum shadow of `(Int(n) ∘ Frob_p)^2 = Frob_{p^2}` on `SL₂`, see
  `TauCeti.DynkinType.ChevalleyDatum.weylFrobenius_weylFrobenius_eq_frobenius_of_rank_eq_one`).

Yet `a1ReflectionIsogeny c` is **not** conjugate under `RootPairing.Aut` to any positive scaling or
to any based endo-isogeny: we prove that `RootPairing.Aut (typeASimplyConnectedRootDatum 1)`
consists solely of `1` and the simple reflection
(`aut_typeASimplyConnectedRootDatum_one_eq_one_or_reflection`), hence is commutative
(`aut_typeASimplyConnectedRootDatum_one_mul_comm`), so every `Aut`-conjugate of
`a1ReflectionIsogeny c` equals `a1ReflectionIsogeny c` itself (`conj_ofEquiv_a1ReflectionIsogeny`)
and fails to preserve `posRoots` (`not_isBased_conj_ofEquiv_a1ReflectionIsogeny`). Consequently,
any classification or normal-form theorem reducing endo-isogenies with scalar-power squares to
positive scalings and diagram/special maps genuinely requires the basedness hypothesis.

## Main definitions and results

* `TauCeti.RootPairingIsogeny.IsBased`: preservation of `posRoots P b` by `f.indexEquiv`, with
  closure under `id`, `1`, `*`, `^`, `smulId`, and surjectivity on `posRoots`.
* `TauCeti.DynkinType.aut_typeASimplyConnectedRootDatum_one_eq_one_or_reflection` and
  `TauCeti.DynkinType.aut_typeASimplyConnectedRootDatum_one_mul_comm`: classification and
  commutativity of `RootPairing.Aut (typeASimplyConnectedRootDatum 1)`.
* `TauCeti.DynkinType.a1ReflectionIsogeny`: the endo-isogeny `ofEquiv s₀ * smulId _ c` of
  `typeASimplyConnectedRootDatum 1`.
* `TauCeti.DynkinType.a1ReflectionIsogeny_mul_self`: its square is `smulId _ (c ^ 2)`.
* `TauCeti.DynkinType.conj_ofEquiv_a1ReflectionIsogeny`,
  `TauCeti.DynkinType.conj_ofEquiv_a1ReflectionIsogeny_ne_of_isBased`, and
  `TauCeti.DynkinType.conj_ofEquiv_a1ReflectionIsogeny_ne_smulId`: invariance under `Aut`
  conjugation and non-conjugacy to any based endo-isogeny or positive scaling.

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §11.
* Schémas en groupes (SGA 3), Exposé XXI, §6.8.
* G. Malle and D. Testerman, *Linear Algebraic Groups and Finite Groups of Lie Type*, Cambridge
  Univ. Press (2011), §21.1 and Example 22.3.
-/

public section

namespace TauCeti

namespace RootPairingIsogeny

section Based

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- **A based endo-isogeny of a root pairing relative to a base `b`**: an endo-isogeny whose index
bijection maps `posRoots P b` into `posRoots P b`. -/
def IsBased (b : P.Base) (f : RootPairingIsogeny P P) : Prop :=
  Set.MapsTo f.indexEquiv (posRoots P b) (posRoots P b)

/-- Unfolding characterization of `RootPairingIsogeny.IsBased`. -/
theorem isBased_def (b : P.Base) (f : RootPairingIsogeny P P) :
    f.IsBased b ↔ Set.MapsTo f.indexEquiv (posRoots P b) (posRoots P b) :=
  Iff.rfl

/-- The identity isogeny `RootPairingIsogeny.id P` is based for every base `b`. -/
@[simp]
theorem isBased_id (b : P.Base) : (RootPairingIsogeny.id P).IsBased b := by
  rw [isBased_def, id_indexEquiv]
  exact Set.mapsTo_id _

/-- The multiplicative unit `1 : RootPairingIsogeny P P` is based for every base `b`. -/
@[simp]
theorem isBased_one (b : P.Base) : (1 : RootPairingIsogeny P P).IsBased b :=
  isBased_id b

/-- Based endo-isogenies are closed under composition (`*`). -/
theorem IsBased.mul {b : P.Base} {f g : RootPairingIsogeny P P}
    (hf : f.IsBased b) (hg : g.IsBased b) : (f * g).IsBased b := by
  rw [isBased_def, indexEquiv_mul]
  exact hf.comp hg

/-- Based endo-isogenies are closed under natural-number powers. -/
theorem IsBased.pow {b : P.Base} {f : RootPairingIsogeny P P}
    (hf : f.IsBased b) (n : ℕ) : (f ^ n).IsBased b := by
  induction n with
  | zero => exact isBased_one b
  | succ n ih =>
      rw [pow_succ']
      exact hf.mul ih

/-- Every based endo-isogeny maps `posRoots P b` bijectively onto itself: if a negative root mapped
into `posRoots P b`, its opposite root would be positive and also map into `posRoots P b`,
violating pointedness of `posRootCone P b`. -/
theorem IsBased.image_posRoots {b : P.Base} {f : RootPairingIsogeny P P}
    (hf : f.IsBased b) :
    f.indexEquiv '' posRoots P b = posRoots P b := by
  ext j
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hf hi
  · intro hj
    let i := f.indexEquiv.symm j
    refine ⟨i, ?_, f.indexEquiv.apply_symm_apply j⟩
    by_contra hi
    have hineg : i ∈ negRoots P b := (not_mem_posRoots_iff_mem_negRoots P b i).mp hi
    let ineg := P.reflectionPerm i i
    have hipos : ineg ∈ posRoots P b := by
      rw [← reflectionPerm_self_mem_negRoots_iff_mem_posRoots]
      have hinv : P.reflectionPerm ineg ineg = i := reflectionPerm_self_involutive P i
      rwa [hinv]
    have hkpos : f.indexEquiv ineg ∈ posRoots P b := hf hipos
    have hsum : (f.exponent i : R) • P.root j +
        (f.exponent ineg : R) • P.root (f.indexEquiv ineg) = 0 := by
      have h0 : P.root i + P.root ineg = 0 := by
        rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, add_neg_cancel]
      have hw := congrArg f.weightMap h0
      rw [map_add, map_zero, f.root_weightMap, f.root_weightMap,
        show f.indexEquiv i = j from f.indexEquiv.apply_symm_apply j] at hw
      exact hw
    let a : ℕ := (f.exponent i).toNat
    let c : ℕ := (f.exponent ineg).toNat
    have ha : 0 < a := Int.lt_toNat.mpr (f.exponent_pos i)
    have ha_eq : (f.exponent i : R) • P.root j = P.root j + (a - 1) • P.root j := by
      have hexp : f.exponent i = (a : ℤ) :=
        (Int.toNat_of_nonneg (f.exponent_pos i).le).symm
      rw [hexp, Int.cast_natCast, Nat.cast_smul_eq_nsmul]
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ a from ha), add_smul, one_smul, add_comm]
    have hc_eq : (f.exponent ineg : R) • P.root (f.indexEquiv ineg) =
        c • P.root (f.indexEquiv ineg) := by
      have hexp : f.exponent ineg = (c : ℤ) :=
        (Int.toNat_of_nonneg (f.exponent_pos ineg).le).symm
      rw [hexp, Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    rw [ha_eq, hc_eq, add_assoc] at hsum
    exact root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone P b hj
      (AddSubmonoid.add_mem _
        (AddSubmonoid.nsmul_mem _ (root_mem_posRootCone_of_mem_posRoots P b hj) _)
        (AddSubmonoid.nsmul_mem _ (root_mem_posRootCone_of_mem_posRoots P b hkpos) _))
      hsum

end Based

section BasedScaling

variable {ι M N : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
  [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
  (P : RootPairing ι ℤ M N)

/-- Every positive integer scaling `smulId P c` is based for every base `b : P.Base`. -/
@[simp]
theorem isBased_smulId (b : P.Base) (c : ℕ+) : (smulId P c).IsBased b := by
  rw [isBased_def, smulId_indexEquiv]
  exact Set.mapsTo_id _

end BasedScaling

end RootPairingIsogeny

namespace DynkinType

/-! ## Automorphisms of the simply connected `A₁` root datum -/

/-- Every `ℤ`-linear equivalence of `Fin 1 → ℤ` is either `+id` or `-id`. -/
private theorem linearEquiv_fin_one_int_eq_id_or_neg (e : (Fin 1 → ℤ) ≃ₗ[ℤ] (Fin 1 → ℤ)) :
    e.toLinearMap = LinearMap.id ∨ e.toLinearMap = -LinearMap.id := by
  let u : Fin 1 → ℤ := fun _ => 1
  have hu : ∀ v : Fin 1 → ℤ, v = v 0 • u := by
    intro v
    funext k
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    simp [u]
  have hmul : e u 0 * e.symm u 0 = 1 := by
    have h1 : e.symm (e u) 0 = 1 := by rw [e.symm_apply_apply]
    conv_lhs at h1 => rw [hu (e u), map_smul, Pi.smul_apply, smul_eq_mul]
    exact h1
  have hunit : IsUnit (e u 0) := IsUnit.of_mul_eq_one (e.symm u 0) hmul
  rcases Int.isUnit_iff.mp hunit with he1 | heneg1
  · refine Or.inl (LinearMap.ext fun v => funext fun k => ?_)
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    calc e v 0
      _ = e (v 0 • u) 0 := by rw [← hu v]
      _ = v 0 * e u 0 := by rw [map_smul, Pi.smul_apply, smul_eq_mul]
      _ = v 0 := by rw [he1, mul_one]
  · refine Or.inr (LinearMap.ext fun v => funext fun k => ?_)
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    calc e v 0
      _ = e (v 0 • u) 0 := by rw [← hu v]
      _ = v 0 * e u 0 := by rw [map_smul, Pi.smul_apply, smul_eq_mul]
      _ = (-LinearMap.id : Module.End ℤ (Fin 1 → ℤ)) v 0 := by
        rw [heneg1]
        simp

/-- On `typeASimplyConnectedRootDatum 1`, the weight map of the simple reflection at node `0` is
`-LinearMap.id`. -/
@[simp]
theorem reflection_typeASimplyConnectedRootDatum_one_weightMap :
    (RootPairing.Equiv.reflection (typeASimplyConnectedRootDatum 1)
      (typeASimpleIndex 1 0)).toHom.weightMap = -LinearMap.id := by
  let P := typeASimplyConnectedRootDatum 1
  let α := typeASimpleIndex 1 0
  apply LinearMap.ext
  intro x
  funext k
  have hk : k = 0 := Subsingleton.elim k 0
  subst hk
  have hroot : P.root α 0 = 2 := by
    rw [root_typeASimpleIndex]
    rfl
  have hcoroot : P.coroot α = Pi.single 0 1 := coroot_typeASimpleIndex 0
  change (P.reflection α x) 0 = -x 0
  rw [RootPairing.reflection_apply, Pi.sub_apply, Pi.smul_apply, hroot, smul_eq_mul]
  dsimp only [RootPairing.coroot', LinearMap.flip_apply, P]
  rw [toLinearMap_typeASimplyConnectedRootDatum, hcoroot, dotProduct_single, mul_one]
  ring

/-- On `typeASimplyConnectedRootDatum 1`, the coweight map of the simple reflection at node `0` is
`-LinearMap.id`. -/
@[simp]
theorem reflection_typeASimplyConnectedRootDatum_one_coweightMap :
    (RootPairing.Equiv.reflection (typeASimplyConnectedRootDatum 1)
      (typeASimpleIndex 1 0)).toHom.coweightMap = -LinearMap.id := by
  let P := typeASimplyConnectedRootDatum 1
  let α := typeASimpleIndex 1 0
  apply LinearMap.ext
  intro y
  funext k
  have hk : k = 0 := Subsingleton.elim k 0
  subst hk
  have hroot : P.root α 0 = 2 := by
    rw [root_typeASimpleIndex]
    rfl
  have hcoroot : P.coroot α = Pi.single 0 1 := coroot_typeASimpleIndex 0
  change (P.coreflection α y) 0 = -y 0
  rw [RootPairing.coreflection_apply, Pi.sub_apply, Pi.smul_apply,
    hcoroot, Pi.single_eq_same, smul_eq_mul]
  have hdot : (RootPairing.root' P α) y = 2 * y 0 := by
    have hlin : (RootPairing.root' P α) y = P.root α ⬝ᵥ y :=
      toLinearMap_typeASimplyConnectedRootDatum (P.root α) y
    rw [hlin]
    simp [dotProduct, hroot]
  rw [hdot]
  ring

/-- **Classification of automorphisms of the simply connected `A₁` root datum**: every automorphism
of `typeASimplyConnectedRootDatum 1` is either `1` or the simple reflection at node `0`. -/
theorem aut_typeASimplyConnectedRootDatum_one_eq_one_or_reflection
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) :
    g = 1 ∨
      g = RootPairing.Equiv.reflection (typeASimplyConnectedRootDatum 1)
        (typeASimpleIndex 1 0) := by
  let P := typeASimplyConnectedRootDatum 1
  rcases linearEquiv_fin_one_int_eq_id_or_neg g.weightEquiv with hpos | hneg
  · refine Or.inl (RootPairing.Equiv.weightHom_injective P ?_)
    apply LinearEquiv.toLinearMap_injective
    exact hpos
  · refine Or.inr (RootPairing.Equiv.weightHom_injective P ?_)
    apply LinearEquiv.toLinearMap_injective
    exact hneg.trans reflection_typeASimplyConnectedRootDatum_one_weightMap.symm

/-- **The automorphism group of `typeASimplyConnectedRootDatum 1` is commutative.** -/
theorem aut_typeASimplyConnectedRootDatum_one_mul_comm
    (g h : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) :
    g * h = h * g := by
  rcases aut_typeASimplyConnectedRootDatum_one_eq_one_or_reflection g with rfl | rfl <;>
    rcases aut_typeASimplyConnectedRootDatum_one_eq_one_or_reflection h with rfl | rfl <;>
    simp

/-! ## The non-based `A₁` reflection isogeny -/

/-- **The reflection-times-scaling endo-isogeny `s₀ ∘ (c • id)` of the simply connected `A₁` root
datum.** At `c = p`, this is the root-datum shadow of `Int(n) ∘ Frob_p` on `SL₂` over an
algebraically closed field of characteristic `p`. -/
def a1ReflectionIsogeny (c : ℕ+) :
    RootPairingIsogeny (typeASimplyConnectedRootDatum 1) (typeASimplyConnectedRootDatum 1) :=
  RootPairingIsogeny.ofEquiv
    (RootPairing.Equiv.reflection (typeASimplyConnectedRootDatum 1) (typeASimpleIndex 1 0)) *
    RootPairingIsogeny.smulId (typeASimplyConnectedRootDatum 1) c

/-- Unfolding formula for `a1ReflectionIsogeny c`. -/
theorem a1ReflectionIsogeny_def (c : ℕ+) :
    a1ReflectionIsogeny c =
      RootPairingIsogeny.ofEquiv
        (RootPairing.Equiv.reflection (typeASimplyConnectedRootDatum 1) (typeASimpleIndex 1 0)) *
        RootPairingIsogeny.smulId (typeASimplyConnectedRootDatum 1) c :=
  (rfl)

/-- The weight map of `a1ReflectionIsogeny c` is `-((c : ℕ) • LinearMap.id)`. -/
@[simp]
theorem a1ReflectionIsogeny_weightMap (c : ℕ+) :
    (a1ReflectionIsogeny c).weightMap = -((c : ℕ) • LinearMap.id) := by
  rw [a1ReflectionIsogeny_def, RootPairingIsogeny.weightMap_mul,
    RootPairingIsogeny.ofEquiv_weightMap, reflection_typeASimplyConnectedRootDatum_one_weightMap,
    RootPairingIsogeny.smulId_weightMap]
  ext x
  simp

/-- The coweight map of `a1ReflectionIsogeny c` is `-((c : ℕ) • LinearMap.id)`. -/
@[simp]
theorem a1ReflectionIsogeny_coweightMap (c : ℕ+) :
    (a1ReflectionIsogeny c).coweightMap = -((c : ℕ) • LinearMap.id) := by
  rw [a1ReflectionIsogeny_def, RootPairingIsogeny.coweightMap_mul,
    RootPairingIsogeny.ofEquiv_coweightMap,
    reflection_typeASimplyConnectedRootDatum_one_coweightMap,
    RootPairingIsogeny.smulId_coweightMap]
  ext y
  simp

/-- The index bijection of `a1ReflectionIsogeny c` is the simple reflection permutation at node
`0`. -/
@[simp]
theorem a1ReflectionIsogeny_indexEquiv (c : ℕ+) :
    (a1ReflectionIsogeny c).indexEquiv =
      (typeASimplyConnectedRootDatum 1).reflectionPerm (typeASimpleIndex 1 0) := by
  rw [a1ReflectionIsogeny_def, RootPairingIsogeny.indexEquiv_mul,
    RootPairingIsogeny.smulId_indexEquiv, Equiv.refl_trans,
    RootPairingIsogeny.ofEquiv_indexEquiv]
  rfl

/-- Every root-rescaling exponent of `a1ReflectionIsogeny c` equals `c`. -/
@[simp]
theorem a1ReflectionIsogeny_exponent (c : ℕ+) (i : Fin (1 * (1 + 1))) :
    (a1ReflectionIsogeny c).exponent i = c := by
  rw [a1ReflectionIsogeny_def, RootPairingIsogeny.exponent_mul,
    RootPairingIsogeny.smulId_exponent, RootPairingIsogeny.ofEquiv_exponent, mul_one]

/-- **Composing `a1ReflectionIsogeny c` with itself gives `smulId _ (c ^ 2)`.** -/
@[simp]
theorem a1ReflectionIsogeny_mul_self (c : ℕ+) :
    a1ReflectionIsogeny c * a1ReflectionIsogeny c =
      RootPairingIsogeny.smulId (typeASimplyConnectedRootDatum 1) (c ^ 2) := by
  let P := typeASimplyConnectedRootDatum 1
  let s := RootPairing.Equiv.reflection P (typeASimpleIndex 1 0)
  have hs : s * s = 1 := mul_eq_one_iff_eq_inv.mpr (RootPairing.Equiv.reflection_inv P _).symm
  have hss : RootPairingIsogeny.ofEquiv s * RootPairingIsogeny.ofEquiv s = 1 := by
    rw [← RootPairingIsogeny.ofEquivHom_apply, ← map_mul, hs, map_one]
  have hcomm := (RootPairingIsogeny.commute_smulId P (RootPairingIsogeny.ofEquiv s) c).eq
  calc a1ReflectionIsogeny c * a1ReflectionIsogeny c
    _ = RootPairingIsogeny.ofEquiv s *
          (RootPairingIsogeny.smulId P c * RootPairingIsogeny.ofEquiv s) *
          RootPairingIsogeny.smulId P c := by
      simp only [a1ReflectionIsogeny_def, s, P, mul_assoc]
    _ = (RootPairingIsogeny.ofEquiv s * RootPairingIsogeny.ofEquiv s) *
          (RootPairingIsogeny.smulId P c * RootPairingIsogeny.smulId P c) := by
      rw [hcomm]
      simp only [mul_assoc]
    _ = RootPairingIsogeny.smulId P (c ^ 2) := by
      rw [hss, one_mul (RootPairingIsogeny.smulId P c * RootPairingIsogeny.smulId P c),
        RootPairingIsogeny.smulId_mul_smulId, ← sq]

/-- Every power of `a1ReflectionIsogeny c` squares to `smulId _ ((c ^ 2) ^ n)`. -/
theorem a1ReflectionIsogeny_pow_mul_self (c : ℕ+) (n : ℕ) :
    a1ReflectionIsogeny c ^ n * a1ReflectionIsogeny c ^ n =
      RootPairingIsogeny.smulId (typeASimplyConnectedRootDatum 1) ((c ^ 2) ^ n) :=
  RootPairingIsogeny.pow_mul_self_eq_smulId (typeASimplyConnectedRootDatum 1)
    (a1ReflectionIsogeny_mul_self c) n

/-- **`a1ReflectionIsogeny c` is not based** with respect to `typeASimplyConnectedBase 1`: it sends
the unique positive root `typeASimpleIndex 1 0` to its negative. -/
theorem not_isBased_a1ReflectionIsogeny (c : ℕ+) :
    ¬ (a1ReflectionIsogeny c).IsBased (typeASimplyConnectedBase 1) := by
  let P := typeASimplyConnectedRootDatum 1
  let B := typeASimplyConnectedBase 1
  let α := typeASimpleIndex 1 0
  intro hBased
  have hαsupp : α ∈ B.support := mem_typeASimplyConnectedBase_support.mpr (by simp [α])
  have hαpos : α ∈ posRoots P B := support_subset_posRoots P B hαsupp
  have himgpos : (a1ReflectionIsogeny c).indexEquiv α ∈ posRoots P B := hBased hαpos
  rw [a1ReflectionIsogeny_indexEquiv] at himgpos
  have himgneg : P.reflectionPerm α α ∈ negRoots P B :=
    (reflectionPerm_self_mem_negRoots_iff_mem_posRoots P B α).mpr hαpos
  exact ((not_mem_posRoots_iff_mem_negRoots P B (P.reflectionPerm α α)).mpr himgneg) himgpos

/-- **`a1ReflectionIsogeny c` is invariant under conjugation by every automorphism of
`typeASimplyConnectedRootDatum 1`**, because `smulId` is central and `Aut` is abelian. -/
@[simp]
theorem conj_ofEquiv_a1ReflectionIsogeny
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) (c : ℕ+) :
    RootPairingIsogeny.ofEquiv g * a1ReflectionIsogeny c * RootPairingIsogeny.ofEquiv g⁻¹ =
      a1ReflectionIsogeny c := by
  let P := typeASimplyConnectedRootDatum 1
  let s := RootPairing.Equiv.reflection P (typeASimpleIndex 1 0)
  have hcomm := (RootPairingIsogeny.commute_smulId P (RootPairingIsogeny.ofEquiv g⁻¹) c).eq
  have hgs : g * s * g⁻¹ = s := by
    rw [aut_typeASimplyConnectedRootDatum_one_mul_comm g s, mul_inv_cancel_right]
  have hgs' :
      RootPairingIsogeny.ofEquiv g * RootPairingIsogeny.ofEquiv s *
          RootPairingIsogeny.ofEquiv g⁻¹ =
        RootPairingIsogeny.ofEquiv s := by
    rw [← RootPairingIsogeny.ofEquivHom_apply, ← RootPairingIsogeny.ofEquivHom_apply,
      ← RootPairingIsogeny.ofEquivHom_apply, ← map_mul, ← map_mul, hgs]
  calc RootPairingIsogeny.ofEquiv g * a1ReflectionIsogeny c * RootPairingIsogeny.ofEquiv g⁻¹
    _ = RootPairingIsogeny.ofEquiv g * RootPairingIsogeny.ofEquiv s *
          (RootPairingIsogeny.smulId P c * RootPairingIsogeny.ofEquiv g⁻¹) := by
      simp only [a1ReflectionIsogeny_def, P, s, mul_assoc]
    _ = (RootPairingIsogeny.ofEquiv g * RootPairingIsogeny.ofEquiv s *
          RootPairingIsogeny.ofEquiv g⁻¹) * RootPairingIsogeny.smulId P c := by
      rw [hcomm]
      simp only [mul_assoc]
    _ = a1ReflectionIsogeny c := by
      rw [hgs', a1ReflectionIsogeny_def]

/-- **No `Aut`-conjugate of `a1ReflectionIsogeny c` is based** with respect to
`typeASimplyConnectedBase 1`. -/
theorem not_isBased_conj_ofEquiv_a1ReflectionIsogeny
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) (c : ℕ+) :
    ¬ (RootPairingIsogeny.ofEquiv g * a1ReflectionIsogeny c *
        RootPairingIsogeny.ofEquiv g⁻¹).IsBased (typeASimplyConnectedBase 1) := by
  rw [conj_ofEquiv_a1ReflectionIsogeny]
  exact not_isBased_a1ReflectionIsogeny c

/-- **No `Aut`-conjugate of `a1ReflectionIsogeny c` equals any based endo-isogeny** (with respect to
`typeASimplyConnectedBase 1`). -/
theorem conj_ofEquiv_a1ReflectionIsogeny_ne_of_isBased
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) (c : ℕ+)
    {f : RootPairingIsogeny (typeASimplyConnectedRootDatum 1) (typeASimplyConnectedRootDatum 1)}
    (hf : f.IsBased (typeASimplyConnectedBase 1)) :
    RootPairingIsogeny.ofEquiv g * a1ReflectionIsogeny c * RootPairingIsogeny.ofEquiv g⁻¹ ≠ f :=
  fun heq => not_isBased_conj_ofEquiv_a1ReflectionIsogeny g c (heq ▸ hf)

/-- **No `Aut`-conjugate of `a1ReflectionIsogeny c` equals any positive scaling `smulId _ d`.** -/
theorem conj_ofEquiv_a1ReflectionIsogeny_ne_smulId
    (g : RootPairing.Aut (typeASimplyConnectedRootDatum 1)) (c d : ℕ+) :
    RootPairingIsogeny.ofEquiv g * a1ReflectionIsogeny c * RootPairingIsogeny.ofEquiv g⁻¹ ≠
      RootPairingIsogeny.smulId (typeASimplyConnectedRootDatum 1) d :=
  conj_ofEquiv_a1ReflectionIsogeny_ne_of_isBased g c
    (RootPairingIsogeny.isBased_smulId (typeASimplyConnectedRootDatum 1)
      (typeASimplyConnectedBase 1) d)

end DynkinType

end TauCeti
