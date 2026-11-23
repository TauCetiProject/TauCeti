/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.NormalSubfield.Basic
public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Factorization
public import TauCeti.NumberTheory.LocalField.Unramified.Maximal
import TauCeti.FieldTheory.Galois.FixedField

/-!
# The unramified part of a finite subextension

For a finite subextension `L` of the separable closure of a nonarchimedean local field `K`,
the intersection of `L` with the maximal unramified extension is the canonical unramified
extension of degree `f(L/K)`. In particular, that canonical field is contained in `L`.
This identifies the unramified base over which extensions with a prescribed residue degree
are totally ramified, as needed in counting extensions by residue degree.

`IntermediateField.inertiaDegree` extends the residue degree to all subextensions, taking
value zero on infinite extensions. It uses the same local-field adapters and totalization as
`IntermediateField.discriminantExponent`. Its invariance under algebra equivalence includes
the infinite case, so residue degree can be used as a weight on isomorphism classes.

Since `K_{f(L/K)}` is Galois over `K` of degree `f(L/K)`, specializing the normal-subfield
automorphism and Galois-orbit decompositions (`IntermediateField.natCard_algEquiv_eq_mul_of_le`
and `IntermediateField.ncard_isomorphic_restrictScalars_mul_natCard_eq`) along
`L.unramifiedExtension_inertiaDegree_le` expresses `#Aut_K(L)` and the number of
`K_{f(L/K)}`-isomorphism classes inside the `K`-isomorphism class of `L` in terms of the
automorphisms of `K_{f(L/K)} / K` that extend to `L`.

## Main results

* `IntermediateField.inertiaDegree_eq_of_algEquiv`: residue degree is an isomorphism invariant,
  with `TauCeti.inertiaDegree_fixedField_stabilizer_smul` and
  `TauCeti.inertiaDegree_fixedField_stabilizer_out` on Galois orbits.
* `IntermediateField.isTotallyRamified_iff_inertiaDegree_eq_one`: a subextension is totally
  ramified exactly when its residue degree is one.
* `IntermediateField.finrank_div_inertiaDegree_pos`: on a finite subextension, `[L : K] / f(L/K)`
  is positive.
* `IntermediateField.unramifiedExtension_inertiaDegree_le`: `K_{f(L/K)} ≤ L` for finite `L`.
* `IntermediateField.inf_maximalUnramifiedExtension`: `L ∩ K^{ur} = K_{f(L/K)}` for finite `L`.
* `IntermediateField.natCard_algEquiv_eq_mul`: decomposition of `Nat.card (L ≃ₐ[K] L)` along
  `K_{f(L/K)} ≤ L`.
* `IntermediateField.natCard_algEquiv_eq_mul_inertiaDegree_of_normal`: for normal `L / K`,
  `#Aut_K(L) = #Aut_{K_{f(L/K)}}(L) · f(L / K)`.
* `IntermediateField.natCard_algEquiv_eq_of_isTotallyRamified`: for totally ramified `L / K`,
  `#Aut_K(L) = #Aut_{K_1}(L)`.
* `IntermediateField.ncard_isomorphic_restrictScalars_mul_natCard_eq_inertiaDegree`: the number
  of `K_{f(L/K)}`-isomorphism representatives in the `K`-isomorphism class of `L`, multiplied by
  the number of automorphisms of `K_{f(L/K)} / K` extending to `L`, equals `f(L / K)`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel TauCeti

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

open Classical in
/-- The residue degree of a subextension of `SeparableClosure K`, using the canonical
local-field structures when the extension is finite, and zero otherwise. -/
def inertiaDegree (L : IntermediateField K (SeparableClosure K)) : ℕ :=
  if _ : Module.Finite K L then
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    TauCeti.inertiaDegree K L
  else 0

/-- On a finite subextension, the totalized residue degree agrees with the residue degree
for its canonical local-field structure. -/
theorem inertiaDegree_eq (L : IntermediateField K (SeparableClosure K))
    [hfin : Module.Finite K L] :
    L.inertiaDegree =
      (letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
      letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
      haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
      TauCeti.inertiaDegree K L) :=
  dite_eq_left hfin

/-- On an infinite subextension the totalized residue degree is zero. -/
theorem inertiaDegree_of_not_finite {L : IntermediateField K (SeparableClosure K)}
    (h : ¬ Module.Finite K L) : L.inertiaDegree = 0 :=
  dite_eq_right h

/-- The residue degree of a finite subextension is positive. -/
theorem inertiaDegree_pos (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] : 0 < L.inertiaDegree := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  exact TauCeti.inertiaDegree_pos

/-- The residue degree of a subextension divides its degree over `K`, including the infinite case
where both vanish. -/
theorem inertiaDegree_dvd_finrank (L : IntermediateField K (SeparableClosure K)) :
    L.inertiaDegree ∣ Module.finrank K L := by
  by_cases h : Module.Finite K L
  · rw [inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    exact ⟨ramificationIndex K L,
      (ramificationIndex_mul_inertiaDegree K L).symm.trans (mul_comm _ _)⟩
  · simp [inertiaDegree_of_not_finite h, Module.finrank_of_not_finite h]

/-- On a finite subextension, the quotient `[L : K] / f(L/K)` (its ramification index) is
positive. -/
theorem finrank_div_inertiaDegree_pos (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] : 0 < Module.finrank K L / L.inertiaDegree := by
  have hmul := Nat.mul_div_cancel' L.inertiaDegree_dvd_finrank
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  by_contra! hle
  rw [Nat.le_zero.mp hle, mul_zero] at hmul
  omega

/-- The residue degree vanishes exactly on infinite subextensions. -/
@[simp]
theorem inertiaDegree_eq_zero_iff (L : IntermediateField K (SeparableClosure K)) :
    L.inertiaDegree = 0 ↔ ¬ Module.Finite K L := by
  by_cases h : Module.Finite K L
  · have := h
    simp [h, (inertiaDegree_pos L).ne']
  · simp [h, inertiaDegree_of_not_finite h]

/-- The residue degree is invariant under `K`-algebra equivalence, including the infinite case. -/
theorem inertiaDegree_eq_of_algEquiv {L M : IntermediateField K (SeparableClosure K)}
    (e : L ≃ₐ[K] M) : L.inertiaDegree = M.inertiaDegree := by
  by_cases hL : Module.Finite K L
  · have : Module.Finite K M := Module.Finite.equiv e.toLinearEquiv
    rw [inertiaDegree_eq, inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) M
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) M
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) M
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) M
    exact TauCeti.inertiaDegree_eq_of_algEquiv K L M e
  · rw [inertiaDegree_of_not_finite hL, inertiaDegree_of_not_finite
      fun h ↦ hL (Module.Finite.equiv e.symm.toLinearEquiv)]

end IntermediateField

namespace TauCeti

/-- Translating a point does not change the residue degree of its stabilizer's fixed field. -/
@[simp]
theorem inertiaDegree_fixedField_stabilizer_smul (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X] (σ : Gal(SeparableClosure K/K)) (x : X) :
    (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x))).inertiaDegree =
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree :=
  IntermediateField.inertiaDegree_eq_of_algEquiv (fixedFieldStabilizerSmulEquiv K σ x)

/-- The residue degree of an orbit's representative fixed field can be computed at any point of the
orbit. -/
theorem inertiaDegree_fixedField_stabilizer_out (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X]
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree =
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree :=
  apply_fixedField_stabilizer_out K IntermediateField.inertiaDegree_eq_of_algEquiv hx

end TauCeti

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A subextension is totally ramified exactly when its totalized residue degree is one; no
finiteness hypothesis is needed, since an infinite subextension has residue degree zero. -/
theorem isTotallyRamified_iff_inertiaDegree_eq_one (L : IntermediateField K (SeparableClosure K)) :
    L.IsTotallyRamified ↔ L.inertiaDegree = 1 := by
  by_cases h : Module.Finite K L
  · rw [L.isTotallyRamified_iff, inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    exact TauCeti.isTotallyRamified_iff_inertiaDegree_eq_one K L
  · rw [inertiaDegree_of_not_finite h]
    exact iff_of_false (fun h' ↦ h h'.finite) zero_ne_one

/-- The bottom subextension has residue degree one. -/
@[simp]
theorem inertiaDegree_bot :
    (⊥ : IntermediateField K (SeparableClosure K)).inertiaDegree = 1 := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) ⊥
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) ⊥
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) ⊥
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) ⊥
  have h := ramificationIndex_mul_inertiaDegree K (⊥ : IntermediateField K (SeparableClosure K))
  rw [IntermediateField.finrank_bot] at h
  exact Nat.eq_one_of_mul_eq_one_left h

/-- The canonical unramified extension of degree `f(L/K)` is contained in every finite
subextension `L`. -/
theorem unramifiedExtension_inertiaDegree_le (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≤ L := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K L
  rw [unramifiedExtension_eq_adjoin_simple TauCeti.inertiaDegree_pos.ne'
    (hζ.map_of_injective L.val.injective), adjoin_simple_le_iff]
  exact ζ.property

/-- The unramified part of a finite subextension is the canonical unramified extension of
its residue degree. No normality hypothesis on `L/K` is required. -/
@[simp]
theorem inf_maximalUnramifiedExtension (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    L ⊓ maximalUnramifiedExtension K (SeparableClosure K) =
      unramifiedExtension K (SeparableClosure K) L.inertiaDegree := by
  apply le_antisymm
  · let E := L ⊓ maximalUnramifiedExtension K (SeparableClosure K)
    have hEL : E ≤ L := inf_le_left
    let _ : Algebra E L := (inclusion hEL).toAlgebra
    have : IsScalarTower K E L := .of_algebraMap_eq fun _ ↦ rfl
    have : Module.Finite K E := Module.Finite.of_injective (inclusion hEL).toLinearMap
      (inclusion_injective hEL)
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) E
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) E
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) E
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) E
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    have : ValuativeExtension E L := (inclusion hEL).valuativeExtension
    have : IsUnramified K E := (E.le_maximalUnramifiedExtension_iff).1 inf_le_right
    calc
      L ⊓ maximalUnramifiedExtension K (SeparableClosure K) =
          unramifiedExtension K (SeparableClosure K) (Module.finrank K E) :=
        E.eq_unramifiedExtension_finrank
      _ ≤ unramifiedExtension K (SeparableClosure K) L.inertiaDegree := by
        rw [inertiaDegree_eq, ← IsUnramified.inertiaDegree_eq_finrank (K := K) (L := E)]
        exact unramifiedExtension_le_of_dvd TauCeti.inertiaDegree_pos.ne'
          (Dvd.intro _ (TauCeti.inertiaDegree_tower (K := K) (L := E) L).symm)
  · exact le_inf (unramifiedExtension_inertiaDegree_le L)
      (unramifiedExtension_le_maximalUnramifiedExtension K (SeparableClosure K) _)

/-- **The automorphism count over the unramified part**: for a finite subextension `L` of
`SeparableClosure K` with canonical unramified base
`U = unramifiedExtension K (SeparableClosure K) L.inertiaDegree`, `Nat.card (L ≃ₐ[K] L)` equals
`Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[U]
extendScalars L.unramifiedExtension_inertiaDegree_le)` times the number of automorphisms of
`U / K` that extend to `L`. -/
theorem natCard_algEquiv_eq_mul (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[
          unramifiedExtension K (SeparableClosure K) L.inertiaDegree]
          extendScalars L.unramifiedExtension_inertiaDegree_le) *
        Nat.card {τ : unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≃ₐ[K]
            unramifiedExtension K (SeparableClosure K) L.inertiaDegree //
          ∃ σ : L ≃ₐ[K] L, ∀ x,
            (σ ⟨x.val, L.unramifiedExtension_inertiaDegree_le x.property⟩ :
              SeparableClosure K) = τ x} :=
  natCard_algEquiv_eq_mul_of_le L.unramifiedExtension_inertiaDegree_le

/-- When `L` is finite and normal over `K`, every automorphism of its unramified part extends to
`L`, so `#Aut_K(L) = #Aut_U(extendScalars L.unramifiedExtension_inertiaDegree_le) · f(L / K)`. -/
theorem natCard_algEquiv_eq_mul_inertiaDegree_of_normal
    (L : IntermediateField K (SeparableClosure K)) [Module.Finite K L] [Normal K L] :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[
          unramifiedExtension K (SeparableClosure K) L.inertiaDegree]
          extendScalars L.unramifiedExtension_inertiaDegree_le) *
        L.inertiaDegree := by
  rw [natCard_algEquiv_eq_mul_of_normal L.unramifiedExtension_inertiaDegree_le,
    natCard_algEquiv_unramifiedExtension L.inertiaDegree_pos.ne']

/-- When `L` is finite and totally ramified over `K`, `Nat.card (L ≃ₐ[K] L)` equals the
cardinality of the `U`-automorphism group of
`extendScalars L.unramifiedExtension_inertiaDegree_le`, where
`U = unramifiedExtension K (SeparableClosure K) L.inertiaDegree`. -/
theorem natCard_algEquiv_eq_of_isTotallyRamified
    (L : IntermediateField K (SeparableClosure K)) [Module.Finite K L]
    (hL : L.IsTotallyRamified) :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars L.unramifiedExtension_inertiaDegree_le ≃ₐ[
          unramifiedExtension K (SeparableClosure K) L.inertiaDegree]
          extendScalars L.unramifiedExtension_inertiaDegree_le) := by
  let U := unramifiedExtension K (SeparableClosure K) L.inertiaDegree
  have hUcard : Nat.card (U ≃ₐ[K] U) = 1 := by
    rw [natCard_algEquiv_unramifiedExtension L.inertiaDegree_pos.ne',
      L.isTotallyRamified_iff_inertiaDegree_eq_one.1 hL]
  have : Subsingleton (U ≃ₐ[K] U) := (Nat.card_eq_one_iff_unique.1 hUcard).1
  have hsub : Nat.card {τ : U ≃ₐ[K] U //
      ∃ σ : L ≃ₐ[K] L, ∀ x,
        (σ ⟨x.val, L.unramifiedExtension_inertiaDegree_le x.property⟩ : SeparableClosure K) =
          τ x} = 1 := by
    refine Nat.card_eq_one_iff_exists.2 ⟨⟨1, ⟨.refl, fun _ ↦ rfl⟩⟩, fun ⟨τ, _⟩ ↦ ?_⟩
    exact Subtype.ext (Subsingleton.elim τ 1)
  rw [L.natCard_algEquiv_eq_mul, hsub, mul_one]

/-- **The Galois orbit count over the unramified part**: for a finite subextension `L` of
`SeparableClosure K` with canonical unramified base
`U = unramifiedExtension K (SeparableClosure K) L.inertiaDegree` and a set `R` containing a unique
`U`-isomorphic representative of every `E : IntermediateField U (SeparableClosure K)` whose
underlying `K`-field is `K`-isomorphic to `L`, the number of such representatives in `R` multiplied
by the number of automorphisms of `U / K` extending to `L` equals `L.inertiaDegree`. -/
theorem ncard_isomorphic_restrictScalars_mul_natCard_eq_inertiaDegree
    (L : IntermediateField K (SeparableClosure K)) [Module.Finite K L]
    {R : Set (IntermediateField (unramifiedExtension K (SeparableClosure K) L.inertiaDegree)
      (SeparableClosure K))}
    (hR : ∀ E : IntermediateField (unramifiedExtension K (SeparableClosure K) L.inertiaDegree)
      (SeparableClosure K), Nonempty (L ≃ₐ[K] E.restrictScalars K) →
        ∃! F, F ∈ R ∧
          Nonempty (E ≃ₐ[unramifiedExtension K (SeparableClosure K) L.inertiaDegree] F)) :
    {E ∈ R | Nonempty (L ≃ₐ[K] E.restrictScalars K)}.ncard *
        Nat.card {τ : unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≃ₐ[K]
            unramifiedExtension K (SeparableClosure K) L.inertiaDegree //
          ∃ σ : L ≃ₐ[K] L, ∀ x,
            (σ ⟨x.val, L.unramifiedExtension_inertiaDegree_le x.property⟩ :
              SeparableClosure K) = τ x} =
      L.inertiaDegree := by
  rw [ncard_isomorphic_restrictScalars_mul_natCard_eq L.unramifiedExtension_inertiaDegree_le hR,
    natCard_algEquiv_unramifiedExtension L.inertiaDegree_pos.ne']

end IntermediateField
