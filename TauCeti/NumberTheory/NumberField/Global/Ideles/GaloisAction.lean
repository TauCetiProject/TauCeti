/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.FiniteAdele
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.GaloisAction
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# Galois action on ideles, idele classes and `S`-ideles

Let `L/K` be an extension of number fields. The automorphism group `Aut(L/K)` acts on the adeles
of `L` by ring automorphisms (`TauCeti.GlobalNumberFields.adeleGaloisAction`), hence on the ideles
`I_L`, and this action fixes the principal ideles setwise, so it descends to the idele class group
`C_L = I_L / Lˣ`. Both actions are recorded in the scope `AdeleGaloisAction`, beside the action on
the adeles, so that they do not compete with other actions on these groups.

For a set `S` of finite places of `K`, the **`S`-ideles** `I_{L,S}` are the ideles of `L` that are
units at every finite place of `L` not above `S`. They form a subgroup stable under `Aut(L/K)`
(`smul_mem_sIdeles`), and the principal ideles in it are exactly those of the `S`-units of `L`
(`unitEmbedding_mem_sIdeles_iff`), the units of `L` at every finite place not above `S`. When the
classes of the primes above `S` generate the ideal class group of `L`, every idele class is the
class of an `S`-idele (`exists_mem_sIdeles_mk_eq`), so that

```text
C_L = I_{L,S} / U_{L,S}.
```

This is the form in which the cohomology of the idele classes of a cyclic extension is computed
from that of the `S`-ideles and the `S`-units.

## Main definitions

* `TauCeti.GlobalNumberFields.ideleMulDistribMulAction`: the action of `Aut(L/K)` on `I_L`.
* `TauCeti.GlobalNumberFields.ideleClassMulDistribMulAction`: the action of `Aut(L/K)` on `C_L`.
* `TauCeti.GlobalNumberFields.sIdeles L S`: the `S`-ideles of `L`.

## Main results

* `TauCeti.GlobalNumberFields.smul_unitEmbedding`: the action on principal ideles is the action
  on `Lˣ`.
* `TauCeti.GlobalNumberFields.smul_mem_sIdeles`: the `S`-ideles are stable under `Aut(L/K)`.
* `TauCeti.GlobalNumberFields.unitEmbedding_mem_sIdeles_iff`: a principal idele is an `S`-idele
  exactly when it comes from an `S`-unit.
* `TauCeti.GlobalNumberFields.exists_mem_sIdeles_mk_eq`: every idele class is the class of an
  `S`-idele, when the primes above `S` generate the class group.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§1–2.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdeleGaloisAction Pointwise TensorProduct

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

/-! ### The Galois action on ideles and idele classes -/

/-- **The Galois action on ideles**: `σ ∈ Aut(L/K)` acts on the units of the adele ring of `L` by
the ring automorphism `TauCeti.GlobalNumberFields.adeleGaloisAction K L σ`. It is a definition
rather than a global instance, available as an instance in the scope `AdeleGaloisAction`. -/
abbrev ideleMulDistribMulAction : MulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup (𝓞 L) L) :=
  Units.mulDistribMulActionRight

scoped[AdeleGaloisAction] attribute [instance]
  TauCeti.GlobalNumberFields.ideleMulDistribMulAction

variable {K L}

/-- The Galois action on an idele is the Galois action on the underlying adele. -/
theorem coe_idele_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup (𝓞 L) L) :
    ((σ • x : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L) = adeleGaloisAction K L σ x := by
  rw [Units.coe_smul, adele_smul_def]

/-- The Galois action on an idele is `Units.map` of the Galois action on adeles, the form in which
it is written elsewhere. -/
theorem idele_smul_def (σ : L ≃ₐ[K] L) (x : IdeleGroup (𝓞 L) L) :
    σ • x = Units.map (adeleGaloisAction K L σ) x :=
  Units.ext (coe_idele_smul σ x)

/-- **The Galois action on principal ideles** is the Galois action on `Lˣ`. -/
@[simp]
theorem smul_unitEmbedding (σ : L ≃ₐ[K] L) (a : Lˣ) :
    σ • IdeleGroup.unitEmbedding (𝓞 L) L a = IdeleGroup.unitEmbedding (𝓞 L) L (σ • a) := by
  refine Units.ext ?_
  rw [coe_idele_smul]
  simp [AlgEquiv.smul_units_def]

/-- The Galois action preserves the principal ideles. -/
theorem smul_mem_principalSubgroup (σ : L ≃ₐ[K] L) {x : IdeleGroup (𝓞 L) L}
    (hx : x ∈ IdeleGroup.principalSubgroup (𝓞 L) L) :
    σ • x ∈ IdeleGroup.principalSubgroup (𝓞 L) L := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨σ • a, (smul_unitEmbedding σ a).symm⟩

variable (K L) in
/-- **The Galois action on idele classes**, induced by the Galois action on ideles, which
preserves the principal ideles. It is a definition rather than a global instance, available as an
instance in the scope `AdeleGaloisAction`. -/
abbrev ideleClassMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup (𝓞 L) L) where
  smul σ := QuotientGroup.map (IdeleGroup.principalSubgroup (𝓞 L) L)
    (IdeleGroup.principalSubgroup (𝓞 L) L)
    (MulDistribMulAction.toMonoidHom (IdeleGroup (𝓞 L) L) σ)
    fun _ hx ↦ Subgroup.mem_comap.2 (smul_mem_principalSubgroup σ hx)
  one_smul c := by
    induction c using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (one_smul _ x)
  mul_smul σ τ c := by
    induction c using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (mul_smul σ τ x)
  smul_mul σ c d := map_mul _ c d
  smul_one σ := map_one _

scoped[AdeleGaloisAction] attribute [instance]
  TauCeti.GlobalNumberFields.ideleClassMulDistribMulAction

/-- The Galois action on the class of an idele is the class of the Galois action on the idele. -/
@[simp]
theorem ideleClass_smul_mk (σ : L ≃ₐ[K] L) (x : IdeleGroup (𝓞 L) L) :
    σ • (x : IdeleClassGroup (𝓞 L) L) = ((σ • x : IdeleGroup (𝓞 L) L) : IdeleClassGroup (𝓞 L) L) :=
  (rfl)

/-! ### `S`-ideles -/

variable (S : Set (HeightOneSpectrum (𝓞 K)))

variable (L) in
/-- **The `S`-ideles.** For a set `S` of finite places of `K`, the ideles of `L` whose component
at every finite place of `L` not above `S` is a unit of the ring of integers of the completion.
Every infinite component is unconstrained. -/
def sIdeles : Subgroup (IdeleGroup (𝓞 L) L) where
  carrier := {x | ∀ w ∉ primesAbove (𝓞 K) (𝓞 L) S,
    Valued.v (w.ideleFiniteCoord x : w.adicCompletion L) = 1}
  mul_mem' {x y} hx hy w hw := by
    rw [map_mul, Units.val_mul, map_mul, hx w hw, hy w hw, one_mul]
  one_mem' w _ := by rw [map_one, Units.val_one, map_one]
  inv_mem' {x} hx w hw := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, hx w hw, inv_one]

variable {S}

/-- An idele is an `S`-idele exactly when its component at every finite place not above `S` has
valuation one. -/
@[simp]
theorem mem_sIdeles_iff {x : IdeleGroup (𝓞 L) L} :
    x ∈ sIdeles L S ↔ ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      Valued.v (w.ideleFiniteCoord x : w.adicCompletion L) = 1 := by
  simp [sIdeles]

variable (S) in
/-- A principal idele is an `S`-idele exactly when it comes from an `S`-unit of `L`, a unit at
every finite place of `L` not above `S`. -/
theorem unitEmbedding_mem_sIdeles_iff (a : Lˣ) :
    IdeleGroup.unitEmbedding (𝓞 L) L a ∈ sIdeles L S ↔
      a ∈ (primesAbove (𝓞 K) (𝓞 L) S).unit L :=
  IdeleGroup.forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff a

/-- **The principal `S`-ideles are those of the `S`-units**: `Lˣ ∩ I_{L,S} = U_{L,S}`. This is
`NumberField.IdeleGroup.mem_principalSubgroup_iff_exists_mem_unit` read on `sIdeles L S`. -/
theorem mem_principalSubgroup_iff_exists_mem_unit_of_mem_sIdeles {x : IdeleGroup (𝓞 L) L}
    (hx : x ∈ sIdeles L S) :
    x ∈ IdeleGroup.principalSubgroup (𝓞 L) L ↔
      ∃ a ∈ (primesAbove (𝓞 K) (𝓞 L) S).unit L,
        IdeleGroup.unitEmbedding (𝓞 L) L a = x :=
  IdeleGroup.mem_principalSubgroup_iff_exists_mem_unit hx

/-- **Every idele class is the class of an `S`-idele**, when the classes of the primes of `L`
above `S` generate the ideal class group of `L`: `I_L = Lˣ · I_{L,S}`. This is
`NumberField.IdeleClassGroup.exists_valued_ideleFiniteCoord_eq_one_and_mk_eq` read on
`sIdeles L S`. -/
theorem exists_mem_sIdeles_mk_eq
    (hS : Subgroup.closure (HeightOneSpectrum.classGroupMk ''
      (primesAbove (𝓞 K) (𝓞 L) S)) = ⊤) (c : IdeleClassGroup (𝓞 L) L) :
    ∃ x ∈ sIdeles L S, (x : IdeleClassGroup (𝓞 L) L) = c :=
  IdeleClassGroup.exists_valued_ideleFiniteCoord_eq_one_and_mk_eq hS c

variable [NumberField K]

/-- The valuation of a component of `σ • x` is the valuation of the component of `x` at the place
`w'` with `σ w' = w`. This is read off the semi-local components above the place of `K` below
`w`, on which `σ` acts by `id ⊗ σ`. -/
private theorem valued_ideleFiniteCoord_smul (σ : L ≃ₐ[K] L)
    (x : IdeleGroup (𝓞 L) L) {v : HeightOneSpectrum (𝓞 K)}
    (w w' : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal})
    (h : w.1.asIdeal = σ • w'.1.asIdeal) :
    Valued.v (w.1.ideleFiniteCoord (σ • x) : w.1.adicCompletion L) =
      Valued.v (w'.1.ideleFiniteCoord x : w'.1.adicCompletion L) := by
  have hmap (z : v.adicCompletion K ⊗[K] L) :
      Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
        (σ : L →ₐ[K] L) z = Algebra.TensorProduct.baseChangeAutHom (v.adicCompletion K) L σ z := by
    induction z using TensorProduct.inductionOn with
    | tmul a y => simp
    | add y z hy hz => rw [map_add, map_add, hy, hz]
  have hw := congrFun (semilocalEquiv_finiteAdeleSemilocalHom (v := v)
    (finiteAdeleEquiv L L σ.toRingEquiv (x : AdeleRing (𝓞 L) L).2)) w
  rw [finiteAdeleSemilocalHom_finiteAdeleEquiv, hmap, semilocalEquiv_baseChangeAutHom σ h,
    semilocalEquiv_finiteAdeleSemilocalHom] at hw
  rw [coe_ideleFiniteCoord, coe_idele_smul, adeleGaloisAction_apply, adeleEquiv_snd,
    ← hw, valued_completionCongr, coe_ideleFiniteCoord]

/-- **The `S`-ideles are stable under the Galois action.** Since `S` is a set of places of `K`,
the places of `L` not above `S` are permuted by `Aut(L/K)`. -/
theorem smul_mem_sIdeles (σ : L ≃ₐ[K] L) {x : IdeleGroup (𝓞 L) L}
    (hx : x ∈ sIdeles L S) :
    σ • x ∈ sIdeles L S := by
  intro w hw
  set v := w.under (𝓞 K)
  let w₀ : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} := ⟨w, inferInstance⟩
  let w' := (liesOverEquivPrimesOver (𝓞 L) v).symm (σ⁻¹ • liesOverEquivPrimesOver (𝓞 L) v w₀)
  have h : w₀.1.asIdeal = σ • w'.1.asIdeal := by
    simp [w', liesOverEquivPrimesOver_symm_apply, coe_smul_primesOver_ringOfIntegers,
      liesOverEquivPrimesOver_apply, smul_inv_smul]
  rw [valued_ideleFiniteCoord_smul σ x w₀ w' h]
  have hv : w'.1.under (𝓞 K) = v := HeightOneSpectrum.ext (w'.2.over).symm
  rw [mem_primesAbove_iff] at hw
  exact hx w'.1 (by rwa [mem_primesAbove_iff, hv])

variable (L S) in
/-- The Galois action of `Aut(L/K)` on the `S`-ideles, restricted from the action on ideles. -/
instance sIdelesMulDistribMulAction : MulDistribMulAction (L ≃ₐ[K] L) (sIdeles L S) :=
  letI : SMul (L ≃ₐ[K] L) (sIdeles L S) := ⟨fun σ x ↦ ⟨σ • x.1, smul_mem_sIdeles σ x.2⟩⟩
  Subtype.coe_injective.mulDistribMulAction (sIdeles L S).subtype fun _ _ ↦ rfl

/-- The Galois action on an `S`-idele is the Galois action on the underlying idele. -/
@[simp]
theorem coe_smul_sIdeles (σ : L ≃ₐ[K] L) (x : sIdeles L S) :
    ((σ • x : sIdeles L S) : IdeleGroup (𝓞 L) L) = σ • (x : IdeleGroup (𝓞 L) L) :=
  (rfl)

/-- **The `S`-units are stable under the Galois action**: they are the units whose principal
ideles are `S`-ideles. -/
theorem smul_mem_unit_primesAbove (σ : L ≃ₐ[K] L) {a : Lˣ}
    (ha : a ∈ (primesAbove (𝓞 K) (𝓞 L) S).unit L) :
    σ • a ∈ (primesAbove (𝓞 K) (𝓞 L) S).unit L := by
  rw [← unitEmbedding_mem_sIdeles_iff, ← smul_unitEmbedding]
  exact smul_mem_sIdeles σ ((unitEmbedding_mem_sIdeles_iff S a).2 ha)

variable (L S) in
/-- The Galois action of `Aut(L/K)` on the `S`-units of `L`, restricted from the action on
`Lˣ`. -/
instance unitPrimesAboveMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((primesAbove (𝓞 K) (𝓞 L) S).unit L) :=
  letI : SMul (L ≃ₐ[K] L) ((primesAbove (𝓞 K) (𝓞 L) S).unit L) :=
    ⟨fun σ a ↦ ⟨σ • a.1, smul_mem_unit_primesAbove σ a.2⟩⟩
  Subtype.coe_injective.mulDistribMulAction (Subgroup.subtype _) fun _ _ ↦ rfl

/-- The Galois action on an `S`-unit is the Galois action on the underlying unit. -/
@[simp]
theorem coe_smul_unit_primesAbove (σ : L ≃ₐ[K] L) (a : (primesAbove (𝓞 K) (𝓞 L) S).unit L) :
    ((σ • a : (primesAbove (𝓞 K) (𝓞 L) S).unit L) : Lˣ) = σ • (a : Lˣ) :=
  (rfl)

end TauCeti.GlobalNumberFields
