/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BasedTorus.Basic

/-!
# Based charts

A **based chart** for `(R, u, Λ)` in an `R`-algebra `B`, not necessarily commutative, is a family
of normalized monomials `M : (I →₀ ℤ) → B` with

* `M 0 = 1`,
* `M a * M b = u ^ Λ(a, b) • M (a + b)`, and
* `R`-linearly independent values.

The first two conditions say that `a ↦ M a` is a representation of the multiplication table of the
based quantum torus `T(R, u, Λ)` (`TauCeti.BasedTorus`), so it extends to an algebra map
`χ : T(R, u, Λ) →ₐ[R] B` with `χ (X^a) = M a`; linear independence says exactly that `χ` is
injective. Conversely every injective algebra map out of the torus has a based chart as its family
of values on the basis monomials. So based charts are the faithful realizations of a based torus,
presented by their normalized monomials (`TauCeti.BasedChart.equivAlgHom`). Since the monomials
of the torus are units, so are the values of a based chart.

In cluster theory a seed carries a based chart: its coordinates `X_i = M(e_i)` are the cluster
variables, and mutation replaces one coordinate. At `u = 1` and `Λ = 0`, and more generally
whenever the factor set `u ^ Λ(a, b)` is trivial, based charts are the injective algebra maps out
of the Laurent ring `TauCeti.LaurentRing R I`, that is the classical Laurent charts
(`TauCeti.BasedChart.equivLaurentRingAlgHom`). For a division ring `B` they are the quantum charts.

## Main definitions

* `TauCeti.BasedChart R u Λ B`: based charts for `(R, u, Λ)` in `B`.
* `TauCeti.BasedChart.coordinate`: the coordinates `X_i = M(e_i)`.
* `TauCeti.BasedChart.toAlgHom`: the algebra map `χ` out of the based quantum torus.
* `TauCeti.BasedChart.eval`: the chart map `f ↦ ∑ a, f a • M a` on coefficient families.
* `TauCeti.BasedChart.ofAlgHom` and `TauCeti.BasedChart.equivAlgHom`: based charts are the
  injective algebra maps out of the based quantum torus.
* `TauCeti.BasedChart.id`: the tautological chart of the based quantum torus in itself.
* `TauCeti.BasedChart.map`: transport along an injective algebra map of the target.
* `TauCeti.BasedChart.reindex`: transport along an equivalence of index types.
* `TauCeti.BasedChart.equivLaurentRingAlgHom`: for a trivial factor set, based charts are the
  injective algebra maps out of the Laurent ring.

## Main results

* `TauCeti.BasedChart.toAlgHom_injective` and `TauCeti.BasedChart.eval_injective`: the chart maps
  are injective.
* `TauCeti.BasedChart.coordinate_mul_coordinate`: for an alternating form the coordinates
  quasi-commute, `X_i * X_j = u ^ (2 Λ i j) • X_j * X_i`.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195
  (2005), §§2–4.
-/

public section

namespace TauCeti

variable {R : Type*} [CommSemiring R] {I : Type*} [Fintype I] [DecidableEq I]

/-- A **based chart** for `(R, u, Λ)` in an `R`-algebra `B`: a family of normalized monomials
`M a`, `a : I →₀ ℤ`, with `M 0 = 1`, the multiplication rule `M a * M b = u ^ Λ(a, b) • M (a + b)`
of the based quantum torus `TauCeti.BasedTorus R u Λ`, and `R`-linearly independent values. The
values are units (`TauCeti.BasedChart.isUnit_monomial`). -/
@[ext]
structure BasedChart (R : Type*) [CommSemiring R] (u : Rˣ) {I : Type*} [Fintype I]
    [DecidableEq I] (Λ : Matrix I I ℤ) (B : Type*) [Semiring B] [Algebra R B] where
  /-- The normalized monomial `M a` of the chart. -/
  monomial : (I →₀ ℤ) → B
  monomial_zero : monomial 0 = 1
  monomial_mul (a b : I →₀ ℤ) :
    monomial a * monomial b = ((u ^ Λ.formPairing a b : Rˣ) : R) • monomial (a + b)
  linearIndependent : LinearIndependent R monomial

namespace BasedChart

variable {u : Rˣ} {Λ : Matrix I I ℤ} {B : Type*} [Semiring B] [Algebra R B]

section ToAlgHom

variable (c : BasedChart R u Λ B)

/-- The algebra map `χ : T(R, u, Λ) →ₐ[R] B` of a based chart, sending `X^a` to `M a`. -/
noncomputable def toAlgHom : BasedTorus R u Λ →ₐ[R] B :=
  BasedTorus.lift c.monomial c.monomial_zero c.monomial_mul

@[simp]
theorem toAlgHom_monomial (a : I →₀ ℤ) : c.toAlgHom (BasedTorus.monomial a) = c.monomial a :=
  BasedTorus.lift_monomial ..

/-- The normalized monomials of a based chart are units. -/
theorem isUnit_monomial (a : I →₀ ℤ) : IsUnit (c.monomial a) := by
  simpa using (BasedTorus.isUnit_monomial (R := R) (u := u) (Λ := Λ) a).map c.toAlgHom

/-- The monomials of a based chart commute up to the scalar `u ^ (Λ(a, b) - Λ(b, a))`. -/
theorem monomial_mul_monomial_comm (a b : I →₀ ℤ) :
    c.monomial a * c.monomial b =
      ((u ^ (Λ.formPairing a b - Λ.formPairing b a) : Rˣ) : R) • (c.monomial b * c.monomial a) := by
  rw [c.monomial_mul, c.monomial_mul, smul_smul, ← Units.val_mul, ← zpow_add, sub_add_cancel,
    add_comm]

/-- The coordinate `X_i = M(e_i)` of a based chart. -/
noncomputable def coordinate (i : I) : B :=
  c.monomial (Finsupp.single i 1)

theorem coordinate_def (i : I) : c.coordinate i = c.monomial (Finsupp.single i 1) :=
  (rfl)

/-- For an alternating form the coordinates of a based chart quasi-commute:
`X_i * X_j = u ^ (2 Λ i j) • X_j * X_i`. -/
theorem coordinate_mul_coordinate (hΛ : Λ.toBilin'.IsAlt) (i j : I) :
    c.coordinate i * c.coordinate j =
      ((u ^ (2 * Λ i j) : Rˣ) : R) • (c.coordinate j * c.coordinate i) := by
  rw [coordinate_def, coordinate_def, monomial_mul_monomial_comm,
    ← (Matrix.isAlt_formPairing_iff.2 hΛ).neg_eq (Finsupp.single i 1), sub_neg_eq_add, ← two_mul,
    Matrix.formPairing_single_single, one_mul, mul_one]

/-- The chart map `f ↦ ∑ a, f a • M a` of a based chart on finitely supported coefficient
families. -/
noncomputable def eval : ((I →₀ ℤ) →₀ R) →ₗ[R] B :=
  Finsupp.linearCombination R c.monomial

@[simp]
theorem eval_single (a : I →₀ ℤ) (r : R) : c.eval (Finsupp.single a r) = r • c.monomial a :=
  Finsupp.linearCombination_single R r a

/-- The chart map is the algebra map of the chart applied to the element of the torus with the
given coordinates in the monomial basis. -/
theorem eval_eq_toAlgHom_comp :
    c.eval = c.toAlgHom.toLinearMap ∘ₗ (BasedTorus.basis R u Λ).repr.symm.toLinearMap :=
  Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring <| by simp

/-- The chart map of a based chart is injective: finite `R`-combinations of the monomials have
unique coefficients. -/
theorem eval_injective : Function.Injective c.eval :=
  c.linearIndependent

/-- The algebra map of a based chart evaluates the coordinates of an element in the monomial
basis. -/
theorem toAlgHom_apply_eq_eval (x : BasedTorus R u Λ) :
    c.toAlgHom x = c.eval ((BasedTorus.basis R u Λ).repr x) := by
  simp [eval_eq_toAlgHom_comp]

/-- The algebra map of a based chart is injective, since it sends the monomial basis to a linearly
independent family. -/
theorem toAlgHom_injective : Function.Injective c.toAlgHom := fun x y h ↦
  (BasedTorus.basis R u Λ).repr.injective <| c.eval_injective <| by
    rwa [← toAlgHom_apply_eq_eval, ← toAlgHom_apply_eq_eval]

end ToAlgHom

section OfAlgHom

/-- The based chart of an injective algebra map out of the based quantum torus: its normalized
monomials are the images of the basis monomials. -/
noncomputable def ofAlgHom (χ : BasedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ) :
    BasedChart R u Λ B where
  monomial a := χ (BasedTorus.monomial a)
  monomial_zero := by simp
  monomial_mul a b := by simp [← map_mul]
  linearIndependent := by
    simpa [Function.comp_def] using (χ.toLinearMap.linearIndependent_iff_of_injOn hχ.injOn).2
      (BasedTorus.basis R u Λ).linearIndependent

@[simp]
theorem ofAlgHom_monomial (χ : BasedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ)
    (a : I →₀ ℤ) : (ofAlgHom χ hχ).monomial a = χ (BasedTorus.monomial a) :=
  (rfl)

@[simp]
theorem toAlgHom_ofAlgHom (χ : BasedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ) :
    (ofAlgHom χ hχ).toAlgHom = χ := by
  ext; simp

@[simp]
theorem ofAlgHom_toAlgHom (c : BasedChart R u Λ B) :
    ofAlgHom c.toAlgHom c.toAlgHom_injective = c := by
  ext; simp

variable (R u Λ B) in
/-- **Based charts are the faithful realizations of the based quantum torus**: `M ↦ χ` with
`χ (X^a) = M a` is a bijection from based charts to injective algebra maps
`T(R, u, Λ) →ₐ[R] B`. -/
noncomputable def equivAlgHom :
    BasedChart R u Λ B ≃ {χ : BasedTorus R u Λ →ₐ[R] B // Function.Injective χ} where
  toFun c := ⟨c.toAlgHom, c.toAlgHom_injective⟩
  invFun χ := ofAlgHom χ.1 χ.2
  left_inv := ofAlgHom_toAlgHom
  right_inv χ := Subtype.ext (toAlgHom_ofAlgHom χ.1 χ.2)

@[simp]
theorem coe_equivAlgHom_apply (c : BasedChart R u Λ B) :
    (equivAlgHom R u Λ B c : BasedTorus R u Λ →ₐ[R] B) = c.toAlgHom :=
  (rfl)

@[simp]
theorem equivAlgHom_symm_apply (χ : {χ : BasedTorus R u Λ →ₐ[R] B // Function.Injective χ}) :
    (equivAlgHom R u Λ B).symm χ = ofAlgHom χ.1 χ.2 :=
  (rfl)

variable (R u Λ) in
/-- The tautological based chart of the based quantum torus in itself: its normalized monomials
are the basis monomials `X^a`. -/
noncomputable def id : BasedChart R u Λ (BasedTorus R u Λ) :=
  ofAlgHom (AlgHom.id R _) Function.injective_id

@[simp]
theorem id_monomial (a : I →₀ ℤ) : (id R u Λ).monomial a = BasedTorus.monomial a :=
  (rfl)

@[simp]
theorem toAlgHom_id : (id R u Λ).toAlgHom = AlgHom.id R (BasedTorus R u Λ) :=
  toAlgHom_ofAlgHom ..

end OfAlgHom

section Map

variable {B' : Type*} [Semiring B'] [Algebra R B']

/-- Transport of a based chart along an injective algebra map of its target. -/
noncomputable def map (c : BasedChart R u Λ B) (f : B →ₐ[R] B') (hf : Function.Injective f) :
    BasedChart R u Λ B' :=
  ofAlgHom (f.comp c.toAlgHom) (by
    rw [AlgHom.coe_comp]
    exact hf.comp c.toAlgHom_injective)

@[simp]
theorem map_monomial (c : BasedChart R u Λ B) (f : B →ₐ[R] B') (hf : Function.Injective f)
    (a : I →₀ ℤ) : (c.map f hf).monomial a = f (c.monomial a) := by
  rw [map, ofAlgHom_monomial, AlgHom.comp_apply, toAlgHom_monomial]

@[simp]
theorem toAlgHom_map (c : BasedChart R u Λ B) (f : B →ₐ[R] B') (hf : Function.Injective f) :
    (c.map f hf).toAlgHom = f.comp c.toAlgHom :=
  toAlgHom_ofAlgHom ..

end Map

section Reindex

variable {I' : Type*} [Fintype I'] [DecidableEq I']

/-- Transport of a based chart along an equivalence `e : I ≃ I'` of index types: the reindexed
chart has the reindexed form and the monomial `M (a ∘ e)` at `a : I' →₀ ℤ`. -/
def reindex (e : I ≃ I') (c : BasedChart R u Λ B) : BasedChart R u (Λ.reindex e e) B where
  monomial a := c.monomial (a.equivMapDomain e.symm)
  monomial_zero := by simpa using c.monomial_zero
  monomial_mul a b := by
    rw [Matrix.formPairing_reindex, c.monomial_mul]
    exact congr_arg (_ • c.monomial ·) ((Finsupp.domCongr e.symm).map_add a b).symm
  linearIndependent := c.linearIndependent.comp _ (Finsupp.domCongr e.symm).injective

@[simp]
theorem reindex_monomial (e : I ≃ I') (c : BasedChart R u Λ B) (a : I' →₀ ℤ) :
    (c.reindex e).monomial a = c.monomial (a.equivMapDomain e.symm) :=
  (rfl)

@[simp]
theorem reindex_coordinate (e : I ≃ I') (c : BasedChart R u Λ B) (i : I) :
    (c.reindex e).coordinate (e i) = c.coordinate i := by
  rw [coordinate_def, coordinate_def, reindex_monomial, Finsupp.equivMapDomain_single,
    Equiv.symm_apply_apply]

end Reindex

section Laurent

variable (B) in
/-- **For a trivial factor set, based charts are the Laurent charts**: `M a = c (X^a)` is a
bijection from injective algebra maps `c` out of the Laurent ring `TauCeti.LaurentRing R I` to
based charts. This applies at `u = 1` (`TauCeti.basedTorusFactor_one`) and for `Λ = 0`
(`TauCeti.basedTorusFactor_zero`). -/
noncomputable def equivLaurentRingAlgHom (h : basedTorusFactor u Λ = 1) :
    BasedChart R u Λ B ≃ {c : LaurentRing R I →ₐ[R] B // Function.Injective c} :=
  (equivAlgHom R u Λ B).trans <|
    ((BasedTorus.laurentRingEquiv h).arrowCongr AlgEquiv.refl).subtypeEquiv fun χ ↦ by
      simp [EquivLike.injective_comp]

@[simp]
theorem equivLaurentRingAlgHom_apply_single (h : basedTorusFactor u Λ = 1)
    (c : BasedChart R u Λ B) (a : I →₀ ℤ) :
    (equivLaurentRingAlgHom B h c : LaurentRing R I →ₐ[R] B) (AddMonoidAlgebra.single a 1) =
      c.monomial a := by
  simp [equivLaurentRingAlgHom]

@[simp]
theorem equivLaurentRingAlgHom_symm_monomial (h : basedTorusFactor u Λ = 1)
    (f : {f : LaurentRing R I →ₐ[R] B // Function.Injective f}) (a : I →₀ ℤ) :
    ((equivLaurentRingAlgHom B h).symm f).monomial a = f.1 (AddMonoidAlgebra.single a 1) := by
  simp [equivLaurentRingAlgHom]

end Laurent

end BasedChart

end TauCeti
