/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.FieldTheory.FunctionField.Belyi.GaloisAction
public import TauCeti.FieldTheory.Galois.FixedField

/-!
# Fields of moduli of algebraic Belyi pairs

Let `k` be a field of characteristic zero, such as `ℂ` or `AlgebraicClosure ℚ`. Its group of
field automorphisms `Aut(k) = Gal(k/ℚ)` acts on isomorphism classes of algebraic Belyi pairs over
`k` by conjugation (`TauCeti.FieldTheory.FunctionField.Belyi.GaloisAction`). The **field of
moduli** of a class `c` is the subfield of `k` fixed by its stabilizer,

```text
U(c) = {σ ∈ Aut(k) | σ • c = c} ,     M(c) = k ^ U(c) .
```

For a representative `(F, t)` of `c`, an automorphism `σ` lies in `U(c)` exactly when the
conjugate pair `(F, t)^σ` is isomorphic to `(F, t)` as a pair, that is by an isomorphism of
function fields commuting with the Belyi maps
(`TauCeti.AlgebraicBelyiPair.IsoClass.smul_mk_eq_mk_iff`, in
`TauCeti.FieldTheory.FunctionField.Belyi.GaloisAction`). At `k = ℂ` these are Köck's relative
moduli field `M(X, t)` and its group `U(X, t)`, through which Belyi pairs over `ℂ` are descended
to number fields; at `k = AlgebraicClosure ℚ` they are the field of moduli and the stabilizer of
a Belyi map under the absolute Galois group.

Since `c` is an isomorphism class, the field of moduli is attached to the class and not to a
representative, and it moves with the class: `M(σ • c) = σ(M(c))`. Every subfield `K ⊆ k` with
`k / K` Galois, as for any subfield of `AlgebraicClosure ℚ`, such that each automorphism fixing
`K` fixes `c` contains the field of moduli. This is how a field of definition of `c` is seen to
contain its field of moduli: the automorphisms fixing it fix a model, hence the class.

The distinguished function `t` is part of the datum. Forgetting it, an automorphism `σ` fixes
the **curve** of a pair `X = (F, t)` when the conjugate function field `F^σ` is isomorphic to `F`
over `k`, with no compatibility with `t` required. These automorphisms form a subgroup
`TauCeti.AlgebraicBelyiPair.curveStabilizer X`, which depends only on the isomorphism class of
`F` over `k`, and its fixed field is the field of moduli of the curve. It is contained in the
field of moduli of the pair.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.IsoClass.fieldOfModuli`: the field of moduli of an isomorphism class
  of algebraic Belyi pairs.
* `TauCeti.AlgebraicBelyiPair.curveStabilizer` and
  `TauCeti.AlgebraicBelyiPair.curveFieldOfModuli`: the automorphisms of `k` fixing the curve of a
  pair, and the field of moduli of the curve.

## Main results

* `TauCeti.AlgebraicBelyiPair.IsoClass.fieldOfModuli_smul`: `M(σ • c) = σ(M(c))`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.fieldOfModuli_le_of_fixingSubgroup_le`: the field of
  moduli lies in every subfield `K` with `k / K` Galois whose automorphisms fix the class.
* `TauCeti.AlgebraicBelyiPair.IsoClass.finrank_fieldOfModuli_eq_trueOrbitSize`: over a Galois
  extension of `ℚ`, and for a class with closed stabilizer, the degree of the field of moduli is
  the true orbit size.
* `TauCeti.AlgebraicBelyiPair.curveStabilizer_eq_of_algEquiv`: the stabilizer of the curve depends
  only on the function field over `k`.
* `TauCeti.AlgebraicBelyiPair.curveFieldOfModuli_le_fieldOfModuli`: the field of moduli of the
  curve is contained in that of the pair.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (2.1) Definition.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, Chapter 3.
-/

public section

universe u

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k]

/-! ### The field of moduli of a pair -/

namespace IsoClass

/-- The **field of moduli** of an isomorphism class `c` of algebraic Belyi pairs over `k`: the
subfield of `k` fixed by every automorphism of `k` that fixes `c`. At `k = ℂ` it is Köck's
relative moduli field `M(X, t)` of a representative `(X, t)`; at `k = AlgebraicClosure ℚ` it is
the field of moduli of the Belyi map. -/
noncomputable def fieldOfModuli (c : IsoClass k) : IntermediateField ℚ k :=
  IntermediateField.fixedField (MulAction.stabilizer (k ≃ₐ[ℚ] k) c)

theorem fieldOfModuli_def (c : IsoClass k) :
    c.fieldOfModuli = IntermediateField.fixedField (MulAction.stabilizer (k ≃ₐ[ℚ] k) c) :=
  (rfl)

@[simp]
theorem mem_fieldOfModuli_iff {c : IsoClass k} {x : k} :
    x ∈ c.fieldOfModuli ↔ ∀ g : k ≃ₐ[ℚ] k, g • c = c → g x = x := by
  simp [fieldOfModuli_def]

/-- The field of moduli of a conjugate class is the conjugate of the field of moduli:
`M(g • c) = g(M(c))`. -/
@[simp]
theorem fieldOfModuli_smul (g : k ≃ₐ[ℚ] k) (c : IsoClass k) :
    (g • c).fieldOfModuli = c.fieldOfModuli.map g.toAlgHom := by
  rw [fieldOfModuli_def, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulEquiv.toMonoidHom_eq_coe, Subgroup.fixedField_map_conj, fieldOfModuli_def]

/-- The field of moduli of a class `c` is contained in every subfield `K` of `k` over which `k`
is Galois, such as any subfield of `AlgebraicClosure ℚ`, and such that every automorphism of `k`
fixing `K` pointwise also fixes `c`. A field of definition of `c` is such a subfield, since the
automorphisms fixing it fix a model of `c`. -/
theorem fieldOfModuli_le_of_fixingSubgroup_le {c : IsoClass k} {K : IntermediateField ℚ k}
    [IsGalois K k] (h : K.fixingSubgroup ≤ MulAction.stabilizer (k ≃ₐ[ℚ] k) c) :
    c.fieldOfModuli ≤ K :=
  (IntermediateField.fixedField_le h).trans (IntermediateField.fixedField_fixingSubgroup K).le

/-- Over a Galois extension `k` of `ℚ`, such as `AlgebraicClosure ℚ`, the degree of the field of
moduli of a class over `ℚ` is its true orbit size, provided its stabilizer is closed in the Krull
topology on `Gal(k/ℚ)`. Both sides are `0` when the orbit is infinite. Without closedness the
statement fails in general: the fixed field only sees the closure of the stabilizer. -/
theorem finrank_fieldOfModuli_eq_trueOrbitSize [IsGalois ℚ k] {c : IsoClass k}
    (hc : IsClosed (MulAction.stabilizer (k ≃ₐ[ℚ] k) c : Set (k ≃ₐ[ℚ] k))) :
    Module.finrank ℚ c.fieldOfModuli = c.trueOrbitSize := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, fieldOfModuli_def,
    InfiniteGalois.fixingSubgroup_fixedField ⟨_, hc⟩, trueOrbitSize_eq_index]

end IsoClass

/-! ### The field of moduli of the curve -/

variable {X Y : AlgebraicBelyiPair k}

variable (X) in
/-- The **stabilizer of the curve** of an algebraic Belyi pair `X = (F, t)`: the automorphisms `g`
of `k` such that the conjugate function field `F^g` is isomorphic to `F` over `k`, with no
compatibility with the Belyi map required. It depends only on `F` as a `k`-algebra
(`TauCeti.AlgebraicBelyiPair.curveStabilizer_eq_of_algEquiv`). -/
def curveStabilizer : Subgroup (k ≃ₐ[ℚ] k) where
  carrier := {g | Nonempty (X.conj (g : k ≃+* k) ≃ₐ[k] X)}
  one_mem' := by
    have h : ((1 : k ≃ₐ[ℚ] k) : k ≃+* k) = RingEquiv.refl k := RingEquiv.ext fun _ ↦ by simp
    rw [Set.mem_ofPred_eq, h]
    exact ⟨(conjRefl X).restrictScalars k⟩
  mul_mem' {g h} := fun ⟨eg⟩ ⟨eh⟩ ↦ by
    have hgh : ((g * h : k ≃ₐ[ℚ] k) : k ≃+* k) = (h : k ≃+* k).trans (g : k ≃+* k) :=
      RingEquiv.ext fun _ ↦ by simp
    rw [Set.mem_ofPred_eq, hgh]
    exact ⟨((conjTrans _ X _).symm.restrictScalars k).trans ((conjCurveAlgEquiv _ eh).trans eg)⟩
  inv_mem' {g} := fun ⟨e⟩ ↦ by
    have hg : RingEquiv.refl k = (g : k ≃+* k).trans ((g⁻¹ : k ≃ₐ[ℚ] k) : k ≃+* k) :=
      RingEquiv.ext fun _ ↦ by simp [AlgEquiv.aut_inv]
    have e' : X ≃ₐ[k] X.conj (RingEquiv.refl k) := ((conjRefl X).restrictScalars k).symm
    rw [hg] at e'
    exact ⟨(e'.trans (((conjTrans _ X _).symm.restrictScalars k).trans
      (conjCurveAlgEquiv _ e))).symm⟩

@[simp]
theorem mem_curveStabilizer_iff {g : k ≃ₐ[ℚ] k} :
    g ∈ X.curveStabilizer ↔ Nonempty (X.conj (g : k ≃+* k) ≃ₐ[k] X) :=
  Iff.rfl

/-- The stabilizer of the curve of a pair depends only on its function field over `k`: pairs with
isomorphic function fields, whatever their Belyi maps, have the same curve stabilizer. -/
theorem curveStabilizer_eq_of_algEquiv (e : X ≃ₐ[k] Y) :
    X.curveStabilizer = Y.curveStabilizer := by
  ext g
  simp only [mem_curveStabilizer_iff]
  exact ⟨fun ⟨f⟩ ↦ ⟨(conjCurveAlgEquiv _ e).symm.trans (f.trans e)⟩,
    fun ⟨f⟩ ↦ ⟨(conjCurveAlgEquiv _ e).trans (f.trans e.symm)⟩⟩

/-- An automorphism of `k` fixing the class of a pair fixes its curve. -/
theorem stabilizer_mk_le_curveStabilizer :
    MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X) ≤ X.curveStabilizer :=
  fun _ hg ↦ (IsoClass.smul_mk_eq_mk_iff.mp hg).map (AlgEquiv.restrictScalars k)

variable (X) in
/-- The **field of moduli of the curve** of an algebraic Belyi pair `X = (F, t)`: the subfield of
`k` fixed by every automorphism `g` of `k` such that `F^g` is isomorphic to `F` over `k`. -/
noncomputable def curveFieldOfModuli : IntermediateField ℚ k :=
  IntermediateField.fixedField X.curveStabilizer

theorem curveFieldOfModuli_def :
    X.curveFieldOfModuli = IntermediateField.fixedField X.curveStabilizer :=
  (rfl)

@[simp]
theorem mem_curveFieldOfModuli_iff {x : k} :
    x ∈ X.curveFieldOfModuli ↔
      ∀ g : k ≃ₐ[ℚ] k, Nonempty (X.conj (g : k ≃+* k) ≃ₐ[k] X) → g x = x := by
  simp [curveFieldOfModuli_def]

/-- Pairs with isomorphic function fields over `k` have the same curve field of moduli. -/
theorem curveFieldOfModuli_eq_of_algEquiv (e : X ≃ₐ[k] Y) :
    X.curveFieldOfModuli = Y.curveFieldOfModuli := by
  rw [curveFieldOfModuli_def, curveFieldOfModuli_def, curveStabilizer_eq_of_algEquiv e]

variable (X) in
/-- The field of moduli of the curve of a pair is contained in the field of moduli of the pair:
remembering the Belyi map can only shrink the stabilizer. -/
theorem curveFieldOfModuli_le_fieldOfModuli :
    X.curveFieldOfModuli ≤ (IsoClass.mk X).fieldOfModuli :=
  IntermediateField.fixedField_le stabilizer_mk_le_curveStabilizer

end AlgebraicBelyiPair

end TauCeti
