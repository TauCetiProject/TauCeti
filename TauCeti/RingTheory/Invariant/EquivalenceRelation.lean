/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Polynomial.Subring
public import Mathlib.RingTheory.QuasiFinite.Basic
public import TauCeti.LinearAlgebra.Charpoly.Projective
public import TauCeti.RingTheory.Norm.Projective
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Invariants of a finite locally free equivalence relation

Two ring homomorphisms `s t : A →+* B` give two morphisms `Spec B ⇉ Spec A`. They form an
**equivalence relation** (`RingHom.IsSpecEquivRel s t`) when, for every commutative ring `T`, the
map sending a point `x : B →+* T` of `Spec B` to the pair of points `(x ∘ s, x ∘ t)` of `Spec A` is
injective and its image is an equivalence relation on the points `A →+* T` of `Spec A`. Thus
`Spec B` is a subfunctor of `Spec A × Spec A` which is reflexive, symmetric and transitive. The
kernel pair `Spec (A ⊗[C] A) ⇉ Spec A` of any `Spec A ⟶ Spec C` is an example
(`RingHom.isSpecEquivRel_tensorProduct`).

The ring of **invariants** of the relation is the equalizer `C = {a : s a = t a}`
(`RingHom.eqLocus s t`); its spectrum is the candidate for the quotient `Spec A / Spec B`. This
file proves that `A` is integral over `C` when `s` is finite locally free, that is, when `B` is a
finite projective `A`-module through `s` (`RingHom.IsSpecEquivRel.isIntegral`), and that the points
of `Spec C` are then the orbits of the relation on the points of `Spec A`.

The proof follows the Stacks Project, Tag 03BK. For `f ∈ A`, let `Q ∈ A[X]` be the reversed
characteristic polynomial `det (1 - X t(f))` of multiplication by `t(f)` on `B`, viewed as an
`A`-module through `s`. By Cayley–Hamilton on the finite projective module `B`
(`LinearMap.exists_aeval_reflect_projectiveCharpolyRev_eq_zero`), a monic reflection `P` of `Q`
kills `t(f)`. The coefficients of `Q` are invariants: pulling `Q` back along `s` gives the
characteristic polynomial of `t(f)` on `B ⊗[A] B`, the ring of `Spec B ×_{s, Spec A, s} Spec B`,
and the shear automorphism `((u, v), (u, w)) ↦ ((v, u), (v, w))` of that scheme, which covers the
inversion `(u, v) ↦ (v, u)` of `Spec B` (`RingHom.IsSpecEquivRel.inv`) and fixes `t(f)` on the
second factor, carries this polynomial to its pullback along `t`. Hence `t (P f) = P(t f) = 0`,
and `t` is injective because the relation is reflexive, so `P f = 0`.

On points, `Spec A ⟶ Spec C` is surjective, and its fibres are the orbits of the relation: two
primes of `A` lie over the same prime of `C` exactly when some prime of `B` relates them
(`RingHom.IsSpecEquivRel.comap_subtype_eqLocus_eq_iff`). If `q` and `q'` are not related, prime
avoidance over the finitely many primes of `B` over `q'` gives `f ∈ q` with `t f` in none of them.
The norm of `t f` along `s` is an invariant
(`RingHom.IsSpecEquivRel.projectiveNorm_mem_eqLocus`), and it lies in `q` but not in `q'`
(`Algebra.projectiveNorm_mem_iff`), contradicting that `q` and `q'` lie over the same prime of `C`.

These are the first steps of the construction of the quotient of an affine scheme by a finite
locally free equivalence relation (SGA 3, Exposé V, Théorème 4.1), which is needed when the
relation does not come from the action of a finite group.

## Main definitions

* `RingHom.IsSpecEquivRel s t`: `Spec B ⇉ Spec A` is an equivalence relation.
* `RingHom.IsSpecEquivRel.inv`: the inversion of the relation, the ring automorphism of `B`
  exchanging `s` and `t`.

## Main results

* `RingHom.IsSpecEquivRel.coeff_projectiveCharpolyRev_mem_eqLocus`: if `s` is finite locally
  free, the coefficients of the reversed characteristic polynomial of multiplication by `t f` are
  invariants.
* `RingHom.IsSpecEquivRel.isIntegral`: if `s` is finite locally free, `A` is integral over the
  ring of invariants `RingHom.eqLocus s t`.
* `RingHom.isSpecEquivRel_tensorProduct`: the kernel pair of `C → A` is an equivalence relation.
* `RingHom.IsSpecEquivRel.projectiveNorm_mem_eqLocus`: if `s` is finite locally free, the norm of
  `t f` along `s` is an invariant.
* `RingHom.IsSpecEquivRel.comap_subtype_eqLocus_surjective` and
  `RingHom.IsSpecEquivRel.comap_subtype_eqLocus_eq_iff`: if `s` is finite locally free, the map
  `Spec A ⟶ Spec C` is surjective and its fibres are the orbits of the relation.

## References

* The Stacks Project, Tag 03BK, and Chapter *Groupoid Schemes*, Section *Finite flat groupoids,
  affine case*.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
-/

public section

universe u

open Polynomial TensorProduct Algebra.TensorProduct

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **Affine equivalence relations.** The two morphisms `Spec B ⇉ Spec A` given by `s t : A →+* B`
form an equivalence relation: for every commutative ring `T` in the universe of `A` and `B`, a point
`x : B →+* T` of `Spec B` is determined by the pair of points `(x ∘ s, x ∘ t)` of `Spec A`, and the
pairs arising in this way form an equivalence relation on the points `A →+* T` of `Spec A`. -/
structure IsSpecEquivRel (s t : A →+* B) : Prop where
  /-- A point of `Spec B` is determined by its two images in `Spec A`. -/
  ext ⦃T : Type u⦄ [CommRing T] ⦃x y : B →+* T⦄ :
    x.comp s = y.comp s → x.comp t = y.comp t → x = y
  /-- Reflexivity: every point `u` of `Spec A` is related to itself. -/
  refl ⦃T : Type u⦄ [CommRing T] (u : A →+* T) : ∃ z : B →+* T, z.comp s = u ∧ z.comp t = u
  /-- Symmetry: if `u` is related to `v`, then `v` is related to `u`. -/
  symm ⦃T : Type u⦄ [CommRing T] (x : B →+* T) :
    ∃ z : B →+* T, z.comp s = x.comp t ∧ z.comp t = x.comp s
  /-- Transitivity: if `u` is related to `v` and `v` to `w`, then `u` is related to `w`. -/
  trans ⦃T : Type u⦄ [CommRing T] (x y : B →+* T) (h : x.comp t = y.comp s) :
    ∃ z : B →+* T, z.comp s = x.comp s ∧ z.comp t = y.comp t

namespace IsSpecEquivRel

variable {s t : A →+* B} (h : s.IsSpecEquivRel t)
include h

/-- The second morphism `t` of an equivalence relation is injective: reflexivity gives a ring
homomorphism `B →+* A` retracting it. -/
theorem injective_right : Function.Injective t := by
  obtain ⟨e, -, het⟩ := h.refl (RingHom.id A)
  exact Function.LeftInverse.injective fun a ↦ congr($het a)

-- the ring endomorphism of `B` exchanging `s` and `t`, given by symmetry
private noncomputable def invHom : B →+* B :=
  (h.symm (RingHom.id B)).choose

private theorem invHom_comp_left : (invHom h).comp s = t :=
  (h.symm (RingHom.id B)).choose_spec.1

private theorem invHom_comp_right : (invHom h).comp t = s :=
  (h.symm (RingHom.id B)).choose_spec.2

private theorem invHom_comp_invHom : (invHom h).comp (invHom h) = RingHom.id B :=
  h.ext (by rw [comp_assoc, invHom_comp_left, invHom_comp_right, id_comp])
    (by rw [comp_assoc, invHom_comp_right, invHom_comp_left, id_comp])

/-- The **inversion** `(u, v) ↦ (v, u)` of an equivalence relation `Spec B ⇉ Spec A`: the ring
automorphism of `B` exchanging `s` and `t`. It is an involution (`inv_inv`). -/
noncomputable def inv : B ≃+* B :=
  .ofRingHom (invHom h) (invHom h) (invHom_comp_invHom h) (invHom_comp_invHom h)

/-- The inversion carries `s` to `t`. -/
@[simp]
theorem inv_apply_left (a : A) : h.inv (s a) = t a :=
  congr($(invHom_comp_left h) a)

/-- The inversion carries `t` to `s`. -/
@[simp]
theorem inv_apply_right (a : A) : h.inv (t a) = s a :=
  congr($(invHom_comp_right h) a)

/-- The inversion is an involution. -/
@[simp]
theorem inv_inv (b : B) : h.inv (h.inv b) = b :=
  congr($(invHom_comp_invHom h) b)

/-- The inversion is its own inverse. -/
@[simp]
theorem inv_symm : h.inv.symm = h.inv := by
  ext b
  exact h.inv.symm_apply_eq.mpr (h.inv_inv b).symm

end IsSpecEquivRel

/-- The **kernel pair** of `Spec A ⟶ Spec C` is an equivalence relation: the two morphisms
`Spec (A ⊗[C] A) ⇉ Spec A` given by the two inclusions relate two points of `Spec A` exactly when
they agree on `C`. -/
theorem isSpecEquivRel_tensorProduct (C A : Type u) [CommRing C] [CommRing A] [Algebra C A] :
    (includeLeftRingHom : A →+* A ⊗[C] A).IsSpecEquivRel includeRight.toRingHom := by
  -- both inclusions agree on `C`
  have hC : (includeLeftRingHom : A →+* A ⊗[C] A).comp (algebraMap C A) =
      (includeRight.toRingHom : A →+* A ⊗[C] A).comp (algebraMap C A) := by
    ext c
    simp [tmul_one_eq_one_tmul]
  refine ⟨fun T _ x y hl hr ↦ ringHom_ext hl hr,
    fun T _ u ↦ ⟨liftRingHom u u rfl, by simp, by simp⟩,
    fun T _ x ↦ ⟨liftRingHom (x.comp includeRight.toRingHom) (x.comp includeLeftRingHom) ?_,
      by simp, by simp⟩,
    fun T _ x y hxy ↦ ⟨liftRingHom (x.comp includeLeftRingHom) (y.comp includeRight.toRingHom) ?_,
      by simp, by simp⟩⟩
  · rw [comp_assoc, comp_assoc, hC]
  · rw [comp_assoc, hC, ← comp_assoc, hxy, comp_assoc, comp_assoc, hC]

namespace IsSpecEquivRel

variable [Algebra A B] {t : A →+* B} (h : (algebraMap A B).IsSpecEquivRel t)
include h

/-! ### The shear automorphism

On `B ⊗[A] B`, the ring of `Spec B ×_{s, Spec A, s} Spec B`, whose points are pairs
`((u, v), (u, w))` of related pairs, the shear automorphism is
`((u, v), (u, w)) ↦ ((v, u), (v, w))`. On functions it sends `b ⊗ 1` to `inv b ⊗ 1` and fixes
`1 ⊗ t a`. -/

-- the point `(v, w)` of `Spec B` with values in `B ⊗[A] B`, by transitivity from `(v, u)` and
-- `(u, w)`
private theorem exists_shearRight :
    ∃ z : B →+* B ⊗[A] B,
      z.comp (algebraMap A B) = includeLeftRingHom.comp t ∧
      z.comp t = includeRight.toRingHom.comp t := by
  obtain ⟨z, hzs, hzt⟩ := h.trans
    ((includeLeftRingHom : B →+* B ⊗[A] B).comp (h.inv : B →+* B)) includeRight.toRingHom
    (by ext a; simp)
  refine ⟨z, ?_, hzt⟩
  rw [hzs]
  ext a
  simp

private noncomputable def shearRight : B →+* B ⊗[A] B :=
  (exists_shearRight h).choose

private theorem shearRight_comp_left :
    (shearRight h).comp (algebraMap A B) = includeLeftRingHom.comp t :=
  (exists_shearRight h).choose_spec.1

private theorem shearRight_comp_right :
    (shearRight h).comp t = (includeRight : B →ₐ[A] B ⊗[A] B).toRingHom.comp t :=
  (exists_shearRight h).choose_spec.2

private noncomputable def shearHom : B ⊗[A] B →+* B ⊗[A] B :=
  liftRingHom ((includeLeftRingHom : B →+* B ⊗[A] B).comp (h.inv : B →+* B))
    (shearRight h) (by rw [comp_assoc, shearRight_comp_left h]; ext a; simp)

private theorem shearHom_tmul (b c : B) : shearHom h (b ⊗ₜ c) = (h.inv b ⊗ₜ 1) * shearRight h c :=
  liftRingHom_tmul _ _ _ b c

private theorem shearHom_tmul_one (b : B) : shearHom h (b ⊗ₜ 1) = h.inv b ⊗ₜ 1 := by
  rw [shearHom_tmul, map_one, mul_one]

private theorem shearRight_apply_right (a : A) : shearRight h (t a) = 1 ⊗ₜ t a :=
  congr($(shearRight_comp_right h) a)

private theorem shearHom_one_tmul_right (a : A) : shearHom h (1 ⊗ₜ t a) = 1 ⊗ₜ t a := by
  rw [shearHom_tmul, map_one, ← Algebra.TensorProduct.one_def, one_mul, shearRight_apply_right]

private theorem shearHom_comp_shearRight :
    (shearHom h).comp (shearRight h) = includeRight.toRingHom := by
  refine h.ext ?_ ?_
  · rw [comp_assoc, shearRight_comp_left h]
    ext a
    -- both sides are `s a ⊗ 1 = 1 ⊗ s a`
    simp [shearHom_tmul_one, tmul_one_eq_one_tmul]
  · ext a
    simp [shearRight_apply_right, shearHom_one_tmul_right]

private theorem shearHom_shearHom (y : B ⊗[A] B) : shearHom h (shearHom h y) = y := by
  have hId : (shearHom h).comp (shearHom h) = RingHom.id (B ⊗[A] B) := by
    refine ringHom_ext ?_ ?_
    · ext b
      simp [shearHom_tmul_one]
    · ext c
      have h1 : shearHom h (1 ⊗ₜ c) = shearRight h c := by
        rw [shearHom_tmul, map_one, ← Algebra.TensorProduct.one_def, one_mul]
      simpa [h1] using congr($(shearHom_comp_shearRight h) c)
  exact congr($hId y)

private theorem ringHomInvPair_inv : RingHomInvPair (h.inv : B →+* B) (h.inv : B →+* B) :=
  ⟨by ext b; simp, by ext b; simp⟩

/-- The shear automorphism of `B ⊗[A] B`, semilinear over the inversion for the `B`-module
structure on the first factor. -/
private noncomputable def shear :
    have := ringHomInvPair_inv h
    B ⊗[A] B ≃ₛₗ[(h.inv : B →+* B)] B ⊗[A] B :=
  have := ringHomInvPair_inv h
  { toFun := shearHom h
    invFun := shearHom h
    map_add' := map_add _
    map_smul' b y := by
      simp only [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, shearHom_tmul_one, RingEquiv.coe_toRingHom]
    left_inv := shearHom_shearHom h
    right_inv := shearHom_shearHom h }

private theorem shear_apply (y : B ⊗[A] B) : shear h y = shearHom h y :=
  rfl

variable [Module.Finite A B] [Module.Projective A B]

/-- **The characteristic polynomial of `t f` has invariant coefficients.** For `f ∈ A`, the
coefficients of the reversed characteristic polynomial `det (1 - X t(f))` of multiplication by
`t f` on `B`, a finite projective `A`-module through `s`, lie in the ring of invariants
`{a : s a = t a}`. -/
theorem coeff_projectiveCharpolyRev_mem_eqLocus (f : A) (i : ℕ) :
    (LinearMap.projectiveCharpolyRev (Algebra.lmul A B (t f))).coeff i ∈
      (algebraMap A B).eqLocus t := by
  have := ringHomInvPair_inv h
  set Q := LinearMap.projectiveCharpolyRev (Algebra.lmul A B (t f))
  -- pulling `Q` back along `s` gives the characteristic polynomial of `1 ⊗ t f` on `B ⊗[A] B`
  have hbc : Q.map (algebraMap A B) =
      LinearMap.projectiveCharpolyRev (Algebra.lmul B (B ⊗[A] B) (1 ⊗ₜ t f)) := by
    rw [← Algebra.baseChange_lmul, LinearMap.projectiveCharpolyRev_baseChange]
  -- which the shear automorphism, covering the inversion, carries to the pullback along `t`
  have hshear := LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq (shear h)
    (f := Algebra.lmul B (B ⊗[A] B) (1 ⊗ₜ t f)) (g := Algebra.lmul B (B ⊗[A] B) (1 ⊗ₜ t f))
    fun y ↦ by
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', LinearMap.mul_apply', shear_apply,
        shear_apply, map_mul, shearHom_one_tmul_right]
  have hQ : Q.map (algebraMap A B) = Q.map t := by
    rw [hbc, hshear, ← hbc, Polynomial.map_map]
    congr 1
    ext a
    simp
  simpa using congr(coeff $hQ i)

/-- **Integrality over the invariants** (Stacks 03BK). If `Spec B ⇉ Spec A` is an equivalence
relation whose first morphism is finite locally free, that is, `B` is a finite projective
`A`-module, then `A` is integral over the ring of invariants `{a : s a = t a}`. -/
@[stacks 03BK]
theorem isIntegral : Algebra.IsIntegral ((algebraMap A B).eqLocus t) A := by
  refine ⟨fun f ↦ ?_⟩
  set Q := LinearMap.projectiveCharpolyRev (Algebra.lmul A B (t f))
  -- by Cayley–Hamilton, a monic reflection `p = Q.reflect n` of `Q` kills `t f`
  obtain ⟨n, hn, hQn⟩ :=
    LinearMap.exists_aeval_reflect_projectiveCharpolyRev_eq_zero (Algebra.lmul A B (t f))
  have h1 : aeval (t f) (Q.reflect n) = 0 := by
    have h1 := congr($hQn 1)
    rw [Polynomial.aeval_algHom_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one]
      at h1
    exact h1
  -- the coefficients of `p` are invariants
  have hS : ((Q.reflect n).coeffs : Set A) ⊆ (algebraMap A B).eqLocus t := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := mem_coeffs_iff.mp hc
    rw [coeff_reflect]
    exact h.coeff_projectiveCharpolyRev_mem_eqLocus f _
  -- so `t (p f) = p (t f) = 0`, and `p f = 0` since `t` is injective
  have hp : (Q.reflect n).map t = (Q.reflect n).map (algebraMap A B) := by
    ext i
    rw [coeff_map, coeff_map, coeff_reflect]
    exact (mem_eqLocus.mp (h.coeff_projectiveCharpolyRev_mem_eqLocus f _)).symm
  have h2 : eval f (Q.reflect n) = 0 := by
    apply h.injective_right
    rw [map_zero, ← h1, aeval_def, ← eval_map, ← hp, eval_map, eval₂_at_apply]
  refine ⟨(Q.reflect n).toSubring _ hS,
    (monic_toSubring _ _ _).mpr (LinearMap.monic_reflect_projectiveCharpolyRev _ hn), ?_⟩
  rw [← eval_map]
  convert h2
  exact map_toSubring _ _ _

/-! ### Points of the quotient

The ring map `C = {a : s a = t a} → A` is injective and, by `isIntegral`, integral, so every prime
of `C` lies under a prime of `A`. Two primes of `A` lie over the same prime of `C` exactly when
they are related by a prime of `B`, so the points of `Spec C` are the orbits of the relation on the
points of `Spec A`. The proof follows the Stacks Project, Groupoid Schemes, Section *Finite flat
groupoids, affine case*: if `q` and `q'` are not related, prime avoidance gives `f ∈ q` with `t f`
outside every prime of `B` over `q'`, and the norm of `t f` is then an invariant lying in `q` but
not in `q'`. -/

/-- The norm of `t f` along `s`, the determinant of multiplication by `t f` on `B` viewed as a
finite projective `A`-module through `s`, is an invariant of the relation. -/
theorem projectiveNorm_mem_eqLocus (f : A) :
    Algebra.projectiveNorm A (t f) ∈ (algebraMap A B).eqLocus t := by
  -- the norm `det (t f)` is the value at `1` of `det (1 - X t (1 - f))`
  have hN : Algebra.projectiveNorm A (t f) =
      (LinearMap.projectiveCharpolyRev (Algebra.lmul A B (t (1 - f)))).eval 1 := by
    rw [LinearMap.eval_one_projectiveCharpolyRev, Algebra.projectiveNorm_apply, map_sub t, map_one,
      map_sub (Algebra.lmul A B), map_one (Algebra.lmul A B), sub_sub_cancel]
  rw [hN, eval_eq_sum_range]
  exact Subring.sum_mem _ fun i _ ↦ by
    simpa using h.coeff_projectiveCharpolyRev_mem_eqLocus (1 - f) i

/-- Every point of `Spec C`, for the ring of invariants `C = {a : s a = t a}`, comes from a point
of `Spec A`. -/
theorem comap_subtype_eqLocus_surjective :
    Function.Surjective (PrimeSpectrum.comap ((algebraMap A B).eqLocus t).subtype) := by
  have := h.isIntegral
  exact Algebra.IsIntegral.comap_surjective ((algebraMap A B).eqLocus t) A

-- If `q` and `q'` are not related, then some `f ∈ q` has `t f` outside every prime of `B` over
-- `q'`.
private theorem exists_mem_forall_notMem_primesOver {q q' : PrimeSpectrum A}
    (hqq' : q.comap ((algebraMap A B).eqLocus t).subtype =
      q'.comap ((algebraMap A B).eqLocus t).subtype)
    (hne : ∀ r : PrimeSpectrum B, r.comap (algebraMap A B) = q → r.comap t ≠ q') :
    ∃ f ∈ q.asIdeal, ∀ P ∈ q'.asIdeal.primesOver B, t f ∉ P := by
  set C := (algebraMap A B).eqLocus t
  have := h.isIntegral
  have hC : t.comp (algebraMap C A) = (algebraMap A B).comp (algebraMap C A) := by
    ext x
    exact x.2.symm
  -- `q` is contained in none of the primes `t⁻¹ P` for `P` over `q'`
  have hnle : ∀ P ∈ q'.asIdeal.primesOver B, ¬ q.asIdeal ≤ P.comap t := by
    rintro P ⟨hP, hPq'⟩ hle
    -- both lie over the same prime of `C`, so by incomparability they are equal
    have hunder : (P.comap t).under C = q.asIdeal.under C := by
      have hq'' := congr(PrimeSpectrum.asIdeal $hqq')
      simp only [PrimeSpectrum.comap_asIdeal] at hq''
      rw [Ideal.under, Ideal.comap_comap, hC, ← Ideal.comap_comap, ← Ideal.under, ← Ideal.under,
        ← hPq'.over]
      exact hq''.symm
    have hq : q.asIdeal = P.comap t := by
      by_contra hne'
      exact (Ideal.IsIntegral.under_lt_under (lt_of_le_of_ne hle hne')).ne hunder.symm
    -- then `P` relates `q'` to `q`, and its image under the inversion relates `q` to `q'`
    refine hne ⟨P.comap (h.inv : B →+* B), Ideal.comap_isPrime _ _⟩ ?_ ?_
    · ext1
      have hinv : (h.inv : B →+* B).comp (algebraMap A B) = t := by
        ext a
        simp
      rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hinv, ← hq]
    · ext1
      have hinv : (h.inv : B →+* B).comp t = algebraMap A B := by
        ext a
        simp
      rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hinv]
      exact hPq'.over.symm
  -- there are finitely many primes over `q'`, so prime avoidance applies
  have hF := Algebra.QuasiFinite.finite_primesOver (S := B) q'.asIdeal
  have hav := (Ideal.subset_union_prime (s := hF.toFinset) (f := fun P ↦ P.comap t) ⊥ ⊥
    (fun P hP _ _ ↦ have := (hF.mem_toFinset.mp hP).1; Ideal.comap_isPrime t P)
    (I := q.asIdeal)).not.mpr (by simpa using hnle)
  simp only [Set.subset_def, not_forall] at hav
  obtain ⟨f, hfq, hf⟩ := hav
  exact ⟨f, hfq, fun P hP hfP ↦ hf (by simpa using ⟨P, hP, hfP⟩)⟩

/-- **The points of the quotient are the orbits of the relation.** Two points `q` and `q'` of
`Spec A` have the same image in `Spec C`, for the ring of invariants `C = {a : s a = t a}`, if and
only if they are related: some point `r` of `Spec B` has `s⁻¹ r = q` and `t⁻¹ r = q'`. -/
theorem comap_subtype_eqLocus_eq_iff {q q' : PrimeSpectrum A} :
    q.comap ((algebraMap A B).eqLocus t).subtype = q'.comap ((algebraMap A B).eqLocus t).subtype ↔
      ∃ r : PrimeSpectrum B, r.comap (algebraMap A B) = q ∧ r.comap t = q' := by
  set C := (algebraMap A B).eqLocus t
  have hC : (algebraMap A B).comp C.subtype = t.comp C.subtype := by
    ext x
    exact x.2
  refine ⟨fun hqq' ↦ ?_, ?_⟩
  · by_contra hne
    push Not at hne
    obtain ⟨f, hfq, hfP⟩ := h.exists_mem_forall_notMem_primesOver hqq' hne
    -- the norm of `t f` is an invariant lying in `q`, through the diagonal point of `Spec B` over
    -- `q`, which contains `t f`
    obtain ⟨e, he, het⟩ := h.refl (RingHom.id A)
    have hNq : Algebra.projectiveNorm A (t f) ∈ q.asIdeal := by
      refine Algebra.projectiveNorm_mem_iff.mpr
        ⟨q.asIdeal.comap e, ⟨Ideal.comap_isPrime _ _, ⟨?_⟩⟩, ?_⟩
      · rw [Ideal.under, Ideal.comap_comap, he, Ideal.comap_id]
      · rwa [Ideal.mem_comap, ← RingHom.comp_apply, het, RingHom.id_apply]
    -- but not in `q'`, since `t f` lies in no prime over `q'`
    have hNq' : Algebra.projectiveNorm A (t f) ∉ q'.asIdeal := fun hN ↦
      have ⟨P, hP, hfP'⟩ := Algebra.projectiveNorm_mem_iff.mp hN
      hfP P hP hfP'
    have hN : (⟨_, h.projectiveNorm_mem_eqLocus f⟩ : C) ∈ (q.comap C.subtype).asIdeal := hNq
    rw [hqq'] at hN
    exact hNq' hN
  · rintro ⟨r, rfl, rfl⟩
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hC]

end IsSpecEquivRel

end RingHom
