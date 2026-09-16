/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Specialization
public import Mathlib.GroupTheory.Index

import Mathlib.Data.Fintype.Perm

/-!
# Resolvent specifications

A resolvent tests whether the Galois group of a polynomial of degree `n`, viewed as a subgroup of
`Equiv.Perm (Fin n)` through a numbering of the roots, lies in a conjugate of a subgroup `H`. The
test is built from an invariant `Φ` in `n` formal roots whose stabilizer under permutation of the
variables is *exactly* `H`: the orbit of `Φ` is then in bijection with the cosets of `H`, and the
factorization of the orbit product records how the Galois group permutes those cosets. A mere
containment of `H` in the stabilizer would not let the resolvent detect `H`.

A `TauCeti.ResolventSpec n` packages this universal data once, independently of any polynomial or
coefficient ring: the subgroup, the integral invariant, the exact stabilizer statement, and the
unique integral expression of the orbit product in the elementary symmetric polynomials. The
last field is determined by the invariant (`MvPolynomial.existsUnique_orbitProduct`), and so is
the subgroup, so a specification is determined by its invariant (`TauCeti.ResolventSpec.ext`).

Specializing at a polynomial `f` over any commutative ring substitutes the signed coefficients of
`f` for the elementary symmetric polynomials. The result is monic of degree the index `[Sₙ : H]`
over every nonzero ring, commutes with every ring morphism applied to the coefficients, and, when
the roots of `f` are listed with multiplicity in a domain, is the orbit product of the values of
the orbit of `Φ` at those roots.

## Main definitions

* `MvPolynomial.renameStabilizer`: the subgroup of permutations of the variables fixing a
  multivariable polynomial.
* `TauCeti.ResolventSpec`: a resolvent specification.
* `TauCeti.ResolventSpec.mk'`: the specification attached to an invariant with prescribed exact
  stabilizer, with its orbit product supplied by the symmetric descent.
* `TauCeti.ResolventSpec.specialize`: the resolvent of a polynomial over a commutative ring.
* `TauCeti.ResolventSpec.rename`: the specification of a renamed invariant, for the conjugate
  subgroup.

## Main results

* `MvPolynomial.card_renameOrbit`: the orbit of an invariant has as many elements as the index of
  its stabilizer.
* `TauCeti.ResolventSpec.ext`: a specification is determined by its invariant.
* `TauCeti.ResolventSpec.specialize_map`: specialization commutes with base change.
* `TauCeti.ResolventSpec.monic_specialize` and `TauCeti.ResolventSpec.natDegree_specialize`: the
  resolvent is monic of degree `[Sₙ : H]`.
* `TauCeti.ResolventSpec.map_specialize_eq_galResolvent`: the resolvent is the orbit product at
  the roots.
* `TauCeti.ResolventSpec.specialize_rename`: renaming the invariant does not change the
  resolvent.
-/

public section

open Polynomial

namespace MvPolynomial

section Stabilizer

variable {σ R : Type*} [CommSemiring R]

/-- The stabilizer of a multivariable polynomial under permutation of its variables. -/
def renameStabilizer (Φ : MvPolynomial σ R) : Subgroup (Equiv.Perm σ) where
  carrier := {e | rename (⇑e) Φ = Φ}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Equiv.Perm.coe_mul, ← rename_rename, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [rename_rename, ← Equiv.Perm.coe_mul, inv_mul_cancel, Equiv.Perm.coe_one, rename_id_apply]

@[simp]
theorem mem_renameStabilizer {Φ : MvPolynomial σ R} {e : Equiv.Perm σ} :
    e ∈ renameStabilizer Φ ↔ rename (⇑e) Φ = Φ :=
  Iff.rfl

/-- A polynomial is symmetric exactly when its stabilizer is the whole symmetric group. -/
theorem renameStabilizer_eq_top_iff {Φ : MvPolynomial σ R} :
    renameStabilizer Φ = ⊤ ↔ Φ.IsSymmetric := by
  simp [Subgroup.eq_top_iff', IsSymmetric]

/-- The stabilizer of a renamed polynomial is the conjugate stabilizer. -/
theorem renameStabilizer_rename (e : Equiv.Perm σ) (Φ : MvPolynomial σ R) :
    renameStabilizer (rename (⇑e) Φ) = (renameStabilizer Φ).map (MulAut.conj e).toMonoidHom := by
  ext τ
  have hcancel (g : Equiv.Perm σ) (p : MvPolynomial σ R) : rename (⇑g⁻¹) (rename (⇑g) p) = p := by
    rw [rename_rename, ← Equiv.Perm.coe_mul, inv_mul_cancel, Equiv.Perm.coe_one, rename_id_apply]
  have hconj : rename (⇑((MulAut.conj e).symm τ)) Φ =
      rename (⇑e⁻¹) (rename (⇑τ) (rename (⇑e) Φ)) := by
    rw [MulAut.conj_symm_apply, rename_rename, rename_rename, Equiv.Perm.coe_mul,
      Equiv.Perm.coe_mul, Function.comp_assoc]
  rw [Subgroup.mem_map_equiv, mem_renameStabilizer, mem_renameStabilizer, hconj]
  constructor
  · intro h
    rw [h, hcancel]
  · intro h
    have h' := congrArg (rename (⇑e⁻¹⁻¹)) h
    rwa [hcancel, inv_inv] at h'

end Stabilizer

variable {n : ℕ}

/-- **Orbit–stabilizer for invariants.** The rename-orbit of `Φ` has as many elements as the
index of its stabilizer. -/
theorem card_renameOrbit (Φ : MvPolynomial (Fin n) ℤ) :
    (renameOrbit Φ).card = (renameStabilizer Φ).index := by
  -- The action of permutations on polynomials by renaming the variables, whose stabilizer and
  -- orbit of `Φ` are `renameStabilizer Φ` and `renameOrbit Φ` by definition.
  let _ : MulAction (Equiv.Perm (Fin n)) (MvPolynomial (Fin n) ℤ) :=
    { smul := fun e p => rename (⇑e) p
      one_smul := rename_id_apply
      mul_smul := fun a b p => (rename_rename (⇑b) (⇑a) p).symm }
  have hstab : MulAction.stabilizer (Equiv.Perm (Fin n)) Φ = renameStabilizer Φ := (rfl)
  have horbit : MulAction.orbit (Equiv.Perm (Fin n)) Φ = ↑(renameOrbit Φ) := by
    ext Ψ
    simp only [MulAction.mem_orbit_iff, Finset.mem_coe, mem_renameOrbit]
    exact Iff.rfl
  rw [← hstab, MulAction.index_stabilizer, horbit, Set.ncard_coe_finset]

/-- A renamed invariant has the same rename-orbit. -/
@[simp]
theorem renameOrbit_rename (e : Equiv.Perm (Fin n)) (Φ : MvPolynomial (Fin n) ℤ) :
    renameOrbit (rename (⇑e) Φ) = renameOrbit Φ := by
  ext Ψ
  simp only [mem_renameOrbit, rename_rename, ← Equiv.Perm.coe_mul]
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ * e, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨τ * e⁻¹, by rw [inv_mul_cancel_right]⟩

/-- A renamed invariant has the same universal resolvent. -/
@[simp]
theorem universalResolvent_rename (e : Equiv.Perm (Fin n)) (Φ : MvPolynomial (Fin n) ℤ) :
    universalResolvent (rename (⇑e) Φ) = universalResolvent Φ := by
  rw [universalResolvent_def, universalResolvent_def, renameOrbit_rename]

/-- A renamed invariant has the same orbit resolvent at every root family. -/
@[simp]
theorem galResolvent_rename {L : Type*} [CommRing L] (e : Equiv.Perm (Fin n))
    (Φ : MvPolynomial (Fin n) ℤ) (x : Fin n → L) :
    galResolvent (rename (⇑e) Φ) x = galResolvent Φ x := by
  rw [galResolvent_def, galResolvent_def, renameOrbit_rename]

end MvPolynomial

namespace TauCeti

open MvPolynomial (renameStabilizer renameOrbit universalResolvent galResolvent)

/-- A **resolvent specification** in degree `n`: a subgroup `H` of `Equiv.Perm (Fin n)`, an
integral invariant `Φ` in `n` formal roots whose stabilizer under renaming is exactly `H`, and the
integral expression of the orbit product of `Φ` in the elementary symmetric polynomials. No
polynomial and no coefficient ring appears; specialization is `ResolventSpec.specialize`. -/
structure ResolventSpec (n : ℕ) where
  /-- The subgroup the resolvent tests membership in. -/
  H : Subgroup (Equiv.Perm (Fin n))
  /-- The invariant polynomial in the formal roots, with integral coefficients. -/
  Φ : MvPolynomial (Fin n) ℤ
  /-- The stabilizer of `Φ` is exactly `H`, not merely contained in it. -/
  stabilizer_eq : ∀ σ : Equiv.Perm (Fin n), MvPolynomial.rename (⇑σ) Φ = Φ ↔ σ ∈ H
  /-- The orbit product of `Φ`, written in the elementary symmetric polynomials. It is
  determined by `Φ`: see `ResolventSpec.orbitProduct_unique`. -/
  orbitProduct : (MvPolynomial (Fin n) ℤ)[X]
  /-- Substituting the elementary symmetric polynomials recovers the universal resolvent. -/
  orbitProduct_esymm : orbitProduct.map (esymmSubst n) = universalResolvent Φ

namespace ResolventSpec

variable {n : ℕ} (spec : ResolventSpec n)

/-- The subgroup of a specification is the stabilizer of its invariant. -/
theorem renameStabilizer_eq : renameStabilizer spec.Φ = spec.H := by
  ext σ
  exact spec.stabilizer_eq σ

/-- The integral expression of the orbit product is unique. -/
theorem orbitProduct_unique {D : (MvPolynomial (Fin n) ℤ)[X]}
    (hD : D.map (esymmSubst n) = universalResolvent spec.Φ) : D = spec.orbitProduct :=
  Polynomial.map_injective _ (esymmSubst_injective n) (hD.trans spec.orbitProduct_esymm.symm)

/-- A specification is determined by its invariant: the subgroup is the stabilizer of the
invariant, and the orbit product is its unique symmetric expression. -/
@[ext]
theorem ext {s t : ResolventSpec n} (h : s.Φ = t.Φ) : s = t := by
  obtain ⟨H, Φ, hH, D, hD⟩ := s
  obtain ⟨H', Φ', hH', D', hD'⟩ := t
  obtain rfl : Φ = Φ' := h
  obtain rfl : H = H' := Subgroup.ext fun σ => (hH σ).symm.trans (hH' σ)
  obtain rfl : D = D' :=
    Polynomial.map_injective _ (esymmSubst_injective n) (hD.trans hD'.symm)
  rfl

/-- The specification attached to an invariant `Φ` whose stabilizer is exactly `H`; its orbit
product is the unique one provided by the symmetric descent. -/
noncomputable def mk' (H : Subgroup (Equiv.Perm (Fin n))) (Φ : MvPolynomial (Fin n) ℤ)
    (h : ∀ σ : Equiv.Perm (Fin n), MvPolynomial.rename (⇑σ) Φ = Φ ↔ σ ∈ H) :
    ResolventSpec n where
  H := H
  Φ := Φ
  stabilizer_eq := h
  orbitProduct := (MvPolynomial.existsUnique_orbitProduct Φ).exists.choose
  orbitProduct_esymm := (MvPolynomial.existsUnique_orbitProduct Φ).exists.choose_spec

@[simp]
theorem mk'_H (H : Subgroup (Equiv.Perm (Fin n))) (Φ : MvPolynomial (Fin n) ℤ)
    (h : ∀ σ : Equiv.Perm (Fin n), MvPolynomial.rename (⇑σ) Φ = Φ ↔ σ ∈ H) :
    (mk' H Φ h).H = H :=
  (rfl)

@[simp]
theorem mk'_Φ (H : Subgroup (Equiv.Perm (Fin n))) (Φ : MvPolynomial (Fin n) ℤ)
    (h : ∀ σ : Equiv.Perm (Fin n), MvPolynomial.rename (⇑σ) Φ = Φ ↔ σ ∈ H) :
    (mk' H Φ h).Φ = Φ :=
  (rfl)

/-- The orbit of the invariant has `[Sₙ : H]` elements. -/
theorem card_renameOrbit : (renameOrbit spec.Φ).card = spec.H.index := by
  rw [MvPolynomial.card_renameOrbit, renameStabilizer_eq]

/-- The integral orbit product is monic. -/
theorem monic_orbitProduct : spec.orbitProduct.Monic :=
  MvPolynomial.monic_of_map_esymmSubst_eq spec.orbitProduct_esymm

/-- The integral orbit product has degree `[Sₙ : H]`. -/
@[simp]
theorem natDegree_orbitProduct : spec.orbitProduct.natDegree = spec.H.index := by
  rw [MvPolynomial.natDegree_of_map_esymmSubst_eq spec.orbitProduct_esymm, card_renameOrbit]

/-! ### Specialization at a polynomial -/

/-- The **resolvent** of a polynomial `f` over a commutative ring `R`: substitute the signed
coefficients of `f` for the elementary symmetric polynomials in the integral orbit product. The
definition is total; it is the orbit product at the roots when `f` is monic of degree `n`
(`ResolventSpec.map_specialize_eq_galResolvent`). -/
noncomputable def specialize (R : Type*) [CommRing R] (f : R[X]) : R[X] :=
  spec.orbitProduct.map (vietaHom n f)

theorem specialize_def (R : Type*) [CommRing R] (f : R[X]) :
    spec.specialize R f = spec.orbitProduct.map (vietaHom n f) :=
  (rfl)

/-- **Base change.** Specialization commutes with a ring morphism applied to the coefficients,
with no hypothesis on `f`. -/
theorem specialize_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R[X]) :
    (spec.specialize R f).map φ = spec.specialize S (f.map φ) := by
  rw [specialize_def, specialize_def, Polynomial.map_map, vietaHom_map]

/-- The resolvent is monic, for every polynomial `f`. -/
theorem monic_specialize (R : Type*) [CommRing R] (f : R[X]) : (spec.specialize R f).Monic :=
  monic_map_vietaHom spec.orbitProduct_esymm f

/-- The resolvent has degree `[Sₙ : H]` over every nonzero ring and for every polynomial `f`:
specialization can make orbit values coincide, but it never lowers the degree. -/
@[simp]
theorem natDegree_specialize (R : Type*) [CommRing R] [Nontrivial R] (f : R[X]) :
    (spec.specialize R f).natDegree = spec.H.index := by
  rw [specialize_def, natDegree_map_vietaHom spec.orbitProduct_esymm, card_renameOrbit]

/-- The resolvent is linear exactly when the specification tests the whole symmetric group. -/
theorem natDegree_specialize_eq_one_iff (R : Type*) [CommRing R] [Nontrivial R] (f : R[X]) :
    (spec.specialize R f).natDegree = 1 ↔ spec.H = ⊤ := by
  rw [natDegree_specialize, Subgroup.index_eq_one]

/-- For a specification testing the trivial subgroup, the resolvent has degree `n!`. -/
theorem natDegree_specialize_of_H_eq_bot (h : spec.H = ⊥) (R : Type*) [CommRing R]
    [Nontrivial R] (f : R[X]) : (spec.specialize R f).natDegree = n.factorial := by
  rw [natDegree_specialize, h, Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]

/-- **The resolvent is the orbit product at the roots.** If `f` is monic of degree `n` and its
image in a domain `L` has roots `x`, listed with multiplicity, then the image of the resolvent of
`f` is the product of `X - Ψ(x)` over the orbit of the invariant. -/
theorem map_specialize_eq_galResolvent {R L : Type*} [CommRing R] [CommRing L] [IsDomain L]
    (φ : R →+* L) {f : R[X]} (hf : f.Monic) (hdeg : f.natDegree = n) {x : Fin n → L}
    (hx : (f.map φ).roots = Finset.univ.val.map x) :
    (spec.specialize R f).map φ = galResolvent spec.Φ x := by
  rw [specialize_map, specialize_def]
  exact map_vietaHom_eq_galResolvent_of_roots spec.orbitProduct_esymm (hf.map φ)
    (by rw [hf.natDegree_map, hdeg]) hx

/-! ### Renaming the invariant -/

/-- The specification of the invariant renamed along `e`. Its subgroup is the conjugate of `H`
by `e`, and its orbit product is unchanged, since the orbit is. -/
noncomputable def rename (e : Equiv.Perm (Fin n)) : ResolventSpec n where
  H := spec.H.map (MulAut.conj e).toMonoidHom
  Φ := MvPolynomial.rename (⇑e) spec.Φ
  stabilizer_eq σ := by
    rw [← MvPolynomial.mem_renameStabilizer, MvPolynomial.renameStabilizer_rename,
      renameStabilizer_eq]
  orbitProduct := spec.orbitProduct
  orbitProduct_esymm := by
    rw [MvPolynomial.universalResolvent_rename]
    exact spec.orbitProduct_esymm

@[simp]
theorem rename_H (e : Equiv.Perm (Fin n)) :
    (spec.rename e).H = spec.H.map (MulAut.conj e).toMonoidHom :=
  (rfl)

@[simp]
theorem rename_Φ (e : Equiv.Perm (Fin n)) :
    (spec.rename e).Φ = MvPolynomial.rename (⇑e) spec.Φ :=
  (rfl)

@[simp]
theorem rename_orbitProduct (e : Equiv.Perm (Fin n)) :
    (spec.rename e).orbitProduct = spec.orbitProduct :=
  (rfl)

/-- Renaming the invariant does not change the resolvent of any polynomial. -/
@[simp]
theorem specialize_rename (e : Equiv.Perm (Fin n)) (R : Type*) [CommRing R] (f : R[X]) :
    (spec.rename e).specialize R f = spec.specialize R f :=
  (rfl)

end ResolventSpec

end TauCeti
