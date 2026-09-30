/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Spec
public import TauCeti.RingTheory.Polynomial.Factors

import Mathlib.FieldTheory.Galois.Infinite
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Roots and factors of a resolvent over the base field

A resolvent specification `TauCeti.ResolventSpec n` carries an invariant `Φ` in `n` formal roots
whose stabilizer under renaming the variables is exactly its subgroup `H ≤ Equiv.Perm (Fin n)`.
Specializing it at a monic separable `f : F[X]` of degree `n` gives
`TauCeti.ResolventSpec.specialize`, a monic polynomial over `F` whose image in an extension `E`
where `f` splits is the product of `X - Ψ(x)` over the orbit of `Φ`, evaluated at the roots `x`
of `f`.

This file compares the roots of that polynomial in `F` with the Galois group. Numbering the roots
of `f` in `E` by an equivalence `e : f.rootSet E ≃ Fin n` turns the image of the Galois action on
the roots into a subgroup of `Equiv.Perm (Fin n)`. An automorphism of `E` over `F` carries the
value of `Φ` at the roots to the value of the invariant renamed along the permutation it induces,
so that value is fixed by the whole Galois group, hence lies in `F`, as soon as the image lies in
`H`; and it is a root of the resolvent. Renaming the invariant, the resolvent therefore has a root
in `F` whenever the image lies in a conjugate of `H`. That direction assumes nothing about the
resolvent.

The converse does assume something. After specialization two distinct elements of the orbit may
take the same value at the roots of `f`, and a root of the resolvent then no longer singles out
one coset of `H`. Separability of the specialized resolvent rules this out: it makes the values of
the orbit pairwise distinct, so a root in `F` is the value of exactly one renamed invariant, that
invariant is fixed by every element of the Galois image, and the image lies in its stabilizer,
which is a conjugate of `H`.

Both readings pass through a numbering of the roots, while the resolvent itself and the property
of being conjugate into `H` do not depend on one.

The root criterion is the linear case of a description of the whole factorization. The value of
the invariant renamed along `τ` depends only on the coset `τH`, and an automorphism of `E` moves it
to the value at the coset obtained by applying the permutation the automorphism induces: the
Galois action on the values of the orbit is the action of the Galois image on the cosets of `H`.
When the resolvent is separable the values at distinct cosets are distinct, so the roots of the
resolvent in `E` are in equivariant bijection with the cosets. Its monic irreducible factors over
`F`, which are the minimal polynomials of these roots, therefore correspond to the orbits of the
Galois image on the cosets, and the degree of a factor is the size of its orbit.

## Main results

* `TauCeti.ResolventSpec.exists_isRoot_specialize_of_le` and
  `TauCeti.ResolventSpec.exists_isRoot_specialize_of_le_map_conj`: a Galois image inside `H`,
  respectively inside a conjugate of `H`, gives the resolvent a root in the base field.
* `TauCeti.ResolventSpec.exists_le_map_conj_of_isRoot_specialize`: conversely, when the
  specialized resolvent is separable, a root of it in the base field confines the Galois image to
  a conjugate of `H`.
* `TauCeti.ResolventSpec.exists_isRoot_specialize_iff_exists_le_map_conj`: the two together, the
  criterion that a separable resolvent provides.
* `TauCeti.ResolventSpec.orbitQuotientEquivFactors`: **the factorization theorem**, the bijection
  between the orbits of the Galois image on the cosets of `H` and the monic irreducible factors of
  a separable resolvent.
* `TauCeti.ResolventSpec.orbitQuotientEquivFactors_apply_mk` and
  `TauCeti.ResolventSpec.orbitQuotientEquivFactors_symm_apply_eq_mk_iff`: the orbit of the coset
  of `τ` goes to the minimal polynomial of the value of the invariant renamed along `τ`.
* `TauCeti.ResolventSpec.natCard_orbit_eq_natDegree_factor`: along it, the size of an orbit is the
  degree of the matching factor.
* `TauCeti.ResolventSpec.map_natDegree_normalizedFactors_specialize`: the multiset of factor
  degrees of a separable resolvent is the multiset of orbit sizes.

## References

* [H. Cohen, *A Course in Computational Algebraic Number Theory*][cohen1993], §6.3.
-/

public section

open Polynomial
open MvPolynomial (renameOrbit galResolvent)

namespace TauCeti

universe u v

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {f : F[X]} {n : ℕ}
  [Fact ((f.map (algebraMap F E)).Splits)]

/-! ## The numbered roots and the Galois action -/

/-- The roots of `f` in `E`, enumerated by `Fin n` through a numbering `e` of the root set. -/
private def rootEnum (e : f.rootSet E ≃ Fin n) (i : Fin n) : E := (e.symm i : f.rootSet E)

-- An automorphism of `E` over `F` moves the numbered roots by the permutation of `Fin n` that
-- its restriction to the Galois group of `f` induces.
private theorem rootEnum_comp_permCongrHom (e : f.rootSet E ≃ Fin n) (ϕ : E ≃ₐ[F] E) :
    rootEnum e ∘ ⇑(e.permCongrHom (Gal.galActionHom f E (Gal.restrict f E ϕ)))
      = ⇑ϕ ∘ rootEnum e := by
  funext i
  simp only [Function.comp_apply, rootEnum, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, Gal.galActionHom_restrict]

-- Consequently it carries the value at the roots of an integral invariant in the formal roots to
-- the value of the invariant renamed along that permutation.
private theorem apply_eval₂_rootEnum (e : f.rootSet E ≃ Fin n) (ϕ : E ≃ₐ[F] E)
    (Ψ : MvPolynomial (Fin n) ℤ) :
    ϕ (MvPolynomial.eval₂ (Int.castRingHom E) (rootEnum e) Ψ)
      = MvPolynomial.eval₂ (Int.castRingHom E) (rootEnum e) (MvPolynomial.rename
          ⇑(e.permCongrHom (Gal.galActionHom f E (Gal.restrict f E ϕ))) Ψ) := by
  have h := MvPolynomial.hom_eval₂ Ψ (Int.castRingHom E) (ϕ : E →+* E) (rootEnum e)
  have hcast : (ϕ : E →+* E).comp (Int.castRingHom E) = Int.castRingHom E :=
    RingHom.ext_int _ _
  rw [hcast] at h
  rw [MvPolynomial.eval₂_rename, rootEnum_comp_permCongrHom, Function.comp_def]
  exact h

-- Over `E` the resolvent of `f` is the orbit product at the numbered roots.
omit [Fact ((f.map (algebraMap F E)).Splits)] in
private theorem map_specialize_eq_galResolvent_rootEnum (spec : ResolventSpec n) (hf : f.Monic)
    (hsep : f.Separable) (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) :
    (spec.specialize F f).map (algebraMap F E) = galResolvent spec.Φ (rootEnum e) := by
  subst hdeg
  exact spec.map_specialize_eq_galResolvent _ hf rfl
    (Polynomial.Separable.roots_map_eq_map_numbering hsep e.symm)

namespace ResolventSpec

variable (spec : ResolventSpec n)

/-! ## From the Galois image to a root of the resolvent -/

/-- **A Galois image inside `H` gives the resolvent a root in the base field.** If, read through
some numbering of the roots of a monic separable `f` of degree `n` in a Galois splitting extension
`E`, the image of the Galois action lies in the subgroup of the specification, then the value of
the invariant at those roots is fixed by every automorphism of `E` over `F`, hence lies in `F`,
and it is a root of the resolvent of `f`.

Nothing is assumed about the resolvent here; the converse
`TauCeti.ResolventSpec.exists_le_map_conj_of_isRoot_specialize` does assume its separability. -/
theorem exists_isRoot_specialize_of_le [IsGalois F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n)
    (hle : (Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom ≤ spec.H) :
    ∃ a : F, (spec.specialize F f).IsRoot a := by
  have hfix : ∀ ϕ : E ≃ₐ[F] E,
      ϕ (MvPolynomial.eval₂ (Int.castRingHom E) (rootEnum e) spec.Φ)
        = MvPolynomial.eval₂ (Int.castRingHom E) (rootEnum e) spec.Φ := by
    intro ϕ
    have hstab : MvPolynomial.rename
        ⇑(e.permCongrHom (Gal.galActionHom f E (Gal.restrict f E ϕ))) spec.Φ = spec.Φ :=
      (spec.stabilizer_eq _).2
        (hle (Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.2 ⟨Gal.restrict f E ϕ, rfl⟩)))
    rw [apply_eval₂_rootEnum, hstab]
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  refine ⟨a, ?_⟩
  have hmem : spec.Φ ∈ renameOrbit spec.Φ := (MvPolynomial.mem_renameOrbit _ _).2 ⟨1, by simp⟩
  have hroot : ((spec.specialize F f).map (algebraMap F E)).IsRoot (algebraMap F E a) := by
    rw [map_specialize_eq_galResolvent_rootEnum spec hf hsep hdeg e, Polynomial.IsRoot,
      MvPolynomial.galResolvent_def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero hmem (by simp [ha])
  rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hroot
  exact (map_eq_zero_iff _ (algebraMap F E).injective).1 hroot

/-- **A Galois image inside a conjugate of `H` gives the resolvent a root in the base field.**
The conjugated subgroup is the subgroup of the specification of the renamed invariant, and
renaming the invariant does not change the resolvent. -/
theorem exists_isRoot_specialize_of_le_map_conj [IsGalois F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) (τ : Equiv.Perm (Fin n))
    (hle : (Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom
      ≤ spec.H.map (MulAut.conj τ).toMonoidHom) :
    ∃ a : F, (spec.specialize F f).IsRoot a := by
  have h := (spec.rename τ).exists_isRoot_specialize_of_le hf hsep hdeg e (by rwa [rename_H])
  rwa [specialize_rename] at h

/-! ## From a root of a separable resolvent to the Galois image -/

/-- **A root of a separable resolvent confines the Galois image to a conjugate of `H`.** Let `f`
be monic and separable of degree `n`, let `E` be a normal splitting extension, and let the
resolvent of `f` for the specification be separable. The values of the orbit of the invariant at
the roots of `f` are then pairwise distinct, so a root of the resolvent in `F` is the value of
exactly one renamed invariant; that invariant is fixed by every element of the Galois image, which
therefore lies in its stabilizer, a conjugate of `H`.

Separability of the resolvent is what makes the argument work, and it cannot be dropped: two
cosets whose invariants happen to collide at the roots of a particular `f` produce a root of the
resolvent in `F` that constrains the Galois image no further. The opposite implication,
`TauCeti.ResolventSpec.exists_isRoot_specialize_of_le_map_conj`, holds unconditionally. -/
theorem exists_le_map_conj_of_isRoot_specialize [Normal F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n)
    (hres : (spec.specialize F f).Separable) {a : F} (ha : (spec.specialize F f).IsRoot a) :
    ∃ τ : Equiv.Perm (Fin n),
      (Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom
        ≤ spec.H.map (MulAut.conj τ).toMonoidHom := by
  have hmap := map_specialize_eq_galResolvent_rootEnum spec hf hsep hdeg e
  have hressep : (galResolvent spec.Φ (rootEnum e)).Separable := hmap ▸ hres.map
  have hroots := MvPolynomial.roots_galResolvent spec.Φ (rootEnum e)
  have hinj := Multiset.inj_on_of_nodup_map (hroots ▸ Polynomial.nodup_roots hressep)
  have hrootv : (galResolvent spec.Φ (rootEnum e)).IsRoot (algebraMap F E a) := by
    rw [← hmap, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]
  have hmemroots : algebraMap F E a ∈ (galResolvent spec.Φ (rootEnum e)).roots :=
    Polynomial.mem_roots'.2 ⟨(MvPolynomial.monic_galResolvent _ _).ne_zero, hrootv⟩
  rw [hroots, Multiset.mem_map] at hmemroots
  obtain ⟨Ψ₀, hΨ₀mem, hΨ₀⟩ := hmemroots
  rw [Finset.mem_val, MvPolynomial.mem_renameOrbit] at hΨ₀mem
  obtain ⟨τ, rfl⟩ := hΨ₀mem
  refine ⟨τ, ?_⟩
  rintro π hπ
  simp only [Subgroup.mem_map, MonoidHom.mem_range] at hπ
  obtain ⟨σ, ⟨g, rfl⟩, rfl⟩ := hπ
  obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective f E g
  have hfix : ϕ (MvPolynomial.eval₂ (Int.castRingHom E) (rootEnum e)
      (MvPolynomial.rename ⇑τ spec.Φ))
      = MvPolynomial.eval₂ (Int.castRingHom E) (rootEnum e) (MvPolynomial.rename ⇑τ spec.Φ) := by
    rw [hΨ₀]
    exact ϕ.commutes a
  have hself : MvPolynomial.rename ⇑τ spec.Φ ∈ renameOrbit spec.Φ :=
    (MvPolynomial.mem_renameOrbit _ _).2 ⟨τ, rfl⟩
  have hother : MvPolynomial.rename
      ⇑(e.permCongrHom (Gal.galActionHom f E (Gal.restrict f E ϕ)))
        (MvPolynomial.rename ⇑τ spec.Φ) ∈ renameOrbit spec.Φ := by
    rw [← MvPolynomial.renameOrbit_rename τ spec.Φ]
    exact (MvPolynomial.mem_renameOrbit _ _).2 ⟨_, rfl⟩
  have hkey : MvPolynomial.rename ⇑(e.permCongrHom (Gal.galActionHom f E (Gal.restrict f E ϕ)))
      (MvPolynomial.rename ⇑τ spec.Φ) = MvPolynomial.rename ⇑τ spec.Φ := by
    refine hinj _ hother _ hself ?_
    rw [← apply_eval₂_rootEnum]
    exact hfix
  rw [← spec.renameStabilizer_eq, ← MvPolynomial.renameStabilizer_rename,
    MvPolynomial.mem_renameStabilizer]
  exact hkey

/-- **The resolvent criterion.** Let `f` be monic and separable of degree `n`, let `E` be a Galois
splitting extension, and let the resolvent of `f` for the specification be separable. The resolvent
then has a root in the base field exactly when the Galois image, read through a numbering of the
roots, lies in a conjugate of the subgroup of the specification. -/
theorem exists_isRoot_specialize_iff_exists_le_map_conj [IsGalois F E] (hf : f.Monic)
    (hsep : f.Separable) (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n)
    (hres : (spec.specialize F f).Separable) :
    (∃ a : F, (spec.specialize F f).IsRoot a) ↔
      ∃ τ : Equiv.Perm (Fin n),
        (Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom
          ≤ spec.H.map (MulAut.conj τ).toMonoidHom :=
  ⟨fun ⟨_, ha⟩ => spec.exists_le_map_conj_of_isRoot_specialize hf hsep hdeg e hres ha,
    fun ⟨τ, hτ⟩ => spec.exists_isRoot_specialize_of_le_map_conj hf hsep hdeg e τ hτ⟩

/-! ## The factorization of a separable resolvent -/

-- The value at the numbered roots of the invariant renamed along a representative of a coset of
-- `H`. Renaming along an element of `H` fixes the invariant, so it depends only on the coset.
private noncomputable def cosetValue (e : f.rootSet E ≃ Fin n) : Equiv.Perm (Fin n) ⧸ spec.H → E :=
  Quotient.lift
    (fun τ => MvPolynomial.eval₂ (Int.castRingHom E) (rootEnum e) (MvPolynomial.rename ⇑τ spec.Φ))
    fun a b hab => by
      have h := congrArg (MvPolynomial.rename ⇑a)
        ((spec.stabilizer_eq _).2 (QuotientGroup.leftRel_apply.1 hab))
      rw [MvPolynomial.rename_rename, ← Equiv.Perm.coe_mul, mul_inv_cancel_left] at h
      exact congrArg _ h.symm

omit [Fact ((f.map (algebraMap F E)).Splits)] in
private theorem cosetValue_mk (e : f.rootSet E ≃ Fin n) (τ : Equiv.Perm (Fin n)) :
    cosetValue spec e τ
      = MvPolynomial.eval₂ (Int.castRingHom E) (rootEnum e) (MvPolynomial.rename ⇑τ spec.Φ) :=
  (rfl)

-- The Galois action on the values of the orbit is the action on the cosets of `H`, transported by
-- the numbering.
private theorem apply_cosetValue (e : f.rootSet E ≃ Fin n) (ϕ : E ≃ₐ[F] E)
    (c : Equiv.Perm (Fin n) ⧸ spec.H) :
    ϕ (cosetValue spec e c)
      = cosetValue spec e (e.permCongrHom (Gal.galActionHom f E (Gal.restrict f E ϕ)) • c) := by
  induction c using QuotientGroup.induction_on with | H τ => ?_
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, cosetValue_mk, cosetValue_mk,
    apply_eval₂_rootEnum, MvPolynomial.rename_rename, ← Equiv.Perm.coe_mul]

-- Each value of the orbit is a root of the resolvent.
omit [Fact ((f.map (algebraMap F E)).Splits)] in
private theorem aeval_cosetValue (hf : f.Monic) (hsep : f.Separable) (hdeg : f.natDegree = n)
    (e : f.rootSet E ≃ Fin n) (c : Equiv.Perm (Fin n) ⧸ spec.H) :
    aeval (cosetValue spec e c) (spec.specialize F f) = 0 := by
  induction c using QuotientGroup.induction_on with | H τ => ?_
  rw [aeval_def, eval₂_eq_eval_map, map_specialize_eq_galResolvent_rootEnum spec hf hsep hdeg e,
    MvPolynomial.galResolvent_def, eval_prod]
  exact Finset.prod_eq_zero ((MvPolynomial.mem_renameOrbit _ _).2 ⟨τ, rfl⟩)
    (by simp [cosetValue_mk])

-- Every root of the resolvent in `E` is a value of the orbit.
omit [Fact ((f.map (algebraMap F E)).Splits)] in
private theorem exists_cosetValue_eq (hf : f.Monic) (hsep : f.Separable) (hdeg : f.natDegree = n)
    (e : f.rootSet E ≃ Fin n) {z : E} (hz : aeval z (spec.specialize F f) = 0) :
    ∃ c, cosetValue spec e c = z := by
  rw [aeval_def, eval₂_eq_eval_map, map_specialize_eq_galResolvent_rootEnum spec hf hsep hdeg e]
    at hz
  have hmem : z ∈ (galResolvent spec.Φ (rootEnum e)).roots :=
    mem_roots'.2 ⟨(MvPolynomial.monic_galResolvent _ _).ne_zero, hz⟩
  rw [MvPolynomial.roots_galResolvent, Multiset.mem_map] at hmem
  obtain ⟨Ψ, hΨ, rfl⟩ := hmem
  obtain ⟨τ, rfl⟩ := (MvPolynomial.mem_renameOrbit _ _).1 hΨ
  exact ⟨τ, cosetValue_mk spec e τ⟩

-- Every monic irreducible factor of the resolvent is the minimal polynomial of a value of the
-- orbit.
omit [Fact ((f.map (algebraMap F E)).Splits)] in
private theorem exists_minpoly_cosetValue_eq (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) (q : (spec.specialize F f).Factors) :
    ∃ c, minpoly F (cosetValue spec e c) = q := by
  have hsplits : ((spec.specialize F f).map (algebraMap F E)).Splits := by
    rw [map_specialize_eq_galResolvent_rootEnum spec hf hsep hdeg e, MvPolynomial.galResolvent_def]
    exact Splits.prod fun _ _ => Splits.X_sub_C _
  have hq : ((q : F[X]).map (algebraMap F E)).Splits :=
    hsplits.of_dvd ((spec.monic_specialize F f).map _).ne_zero (Polynomial.map_dvd _ q.dvd)
  have hqdeg : ((q : F[X]).map (algebraMap F E)).natDegree ≠ 0 := by
    rw [natDegree_map]
    exact q.irreducible.natDegree_pos.ne'
  obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero (hq.roots_ne_zero hqdeg)
  have hzq : aeval z (q : F[X]) = 0 := by
    rw [aeval_def, ← eval_map]
    exact (mem_roots (q.monic.map (algebraMap F E)).ne_zero).mp hz
  obtain ⟨c, rfl⟩ := exists_cosetValue_eq spec hf hsep hdeg e
    (aeval_eq_zero_of_dvd_aeval_eq_zero q.dvd hzq)
  exact ⟨c, (minpoly.eq_of_irreducible_of_monic q.irreducible hzq q.monic).symm⟩

-- A separable resolvent takes pairwise distinct values on the cosets of `H`.
omit [Fact ((f.map (algebraMap F E)).Splits)] in
private theorem cosetValue_injective (hf : f.Monic) (hsep : f.Separable) (hdeg : f.natDegree = n)
    (e : f.rootSet E ≃ Fin n) (hres : (spec.specialize F f).Separable) :
    Function.Injective (cosetValue spec e) := by
  have hmap := map_specialize_eq_galResolvent_rootEnum spec hf hsep hdeg e
  have hressep : (galResolvent spec.Φ (rootEnum e)).Separable := hmap ▸ hres.map
  have hinj := Multiset.inj_on_of_nodup_map
    (MvPolynomial.roots_galResolvent spec.Φ (rootEnum e) ▸ nodup_roots hressep)
  have hmem (τ : Equiv.Perm (Fin n)) : MvPolynomial.rename ⇑τ spec.Φ ∈ renameOrbit spec.Φ :=
    (MvPolynomial.mem_renameOrbit _ _).2 ⟨τ, rfl⟩
  intro c d hcd
  induction c using QuotientGroup.induction_on with | H a => ?_
  induction d using QuotientGroup.induction_on with | H b => ?_
  rw [cosetValue_mk, cosetValue_mk] at hcd
  have h := hinj _ (hmem a) _ (hmem b) hcd
  rw [QuotientGroup.eq, ← spec.stabilizer_eq, Equiv.Perm.coe_mul, ← MvPolynomial.rename_rename,
    ← h, MvPolynomial.rename_rename, ← Equiv.Perm.coe_mul, inv_mul_cancel, Equiv.Perm.coe_one,
    MvPolynomial.rename_id_apply]

-- Two values of the orbit have the same minimal polynomial exactly when their cosets lie in one
-- orbit of the Galois image.
private theorem minpoly_cosetValue_eq_iff [Normal F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) (hres : (spec.specialize F f).Separable)
    {c d : Equiv.Perm (Fin n) ⧸ spec.H} :
    minpoly F (cosetValue spec e c) = minpoly F (cosetValue spec e d) ↔
      c ∈ MulAction.orbit ((Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom) d := by
  constructor
  · intro h
    obtain ⟨ϕ, hϕ⟩ := (Normal.minpoly_eq_iff_mem_orbit E).1 h
    refine MulAction.mem_orbit_iff.2
      ⟨⟨_, Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.2 ⟨Gal.restrict f E ϕ, rfl⟩)⟩,
        cosetValue_injective spec hf hsep hdeg e hres ?_⟩
    rw [Subgroup.smul_def]
    exact (apply_cosetValue spec e ϕ d).symm.trans hϕ
  · intro h
    obtain ⟨⟨π, hπ⟩, rfl⟩ := MulAction.mem_orbit_iff.1 h
    simp only [Subgroup.mem_map, MonoidHom.mem_range] at hπ
    obtain ⟨σ, ⟨g, rfl⟩, rfl⟩ := hπ
    obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective f E g
    rw [Subgroup.smul_def]
    exact (congrArg (minpoly F) (apply_cosetValue spec e ϕ d)).symm.trans
      (minpoly.algEquiv_eq ϕ _)

-- The roots of the minimal polynomial of a value of the orbit are the values on the orbit of its
-- coset under the Galois image.
private theorem image_cosetValue_orbit [Normal F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) (hres : (spec.specialize F f).Separable)
    (c : Equiv.Perm (Fin n) ⧸ spec.H) :
    cosetValue spec e ''
        MulAction.orbit ((Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom) c
      = (minpoly F (cosetValue spec e c)).rootSet E := by
  have hint : IsIntegral F (cosetValue spec e c) := Algebra.IsIntegral.isIntegral _
  ext z
  rw [mem_rootSet]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [← minpoly_cosetValue_eq_iff spec hf hsep hdeg e hres] at hd
    exact ⟨minpoly.ne_zero hint, hd ▸ minpoly.aeval F _⟩
  · rintro ⟨-, hz⟩
    have hdvd := minpoly.dvd F _ (aeval_cosetValue spec hf hsep hdeg e c)
    obtain ⟨d, rfl⟩ := exists_cosetValue_eq spec hf hsep hdeg e
      (aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hz)
    refine ⟨d, (minpoly_cosetValue_eq_iff spec hf hsep hdeg e hres).1 ?_, rfl⟩
    exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hz
      (minpoly.monic hint)).symm

/-- **The factorization theorem for a separable resolvent.** Let `f` be monic and separable of
degree `n`, let `E` be a normal splitting extension, number the roots of `f` in `E` by `e`, and
let the resolvent of `f` for the specification be separable. The orbits of the Galois image, read
through `e`, on the cosets of `H` are then in bijection with the monic irreducible factors of the
resolvent over `F`: the orbit of the coset of `τ` goes to the minimal polynomial of the value at
the roots of the invariant renamed along `τ`.

The degree of each factor is the size of the matching orbit,
`TauCeti.ResolventSpec.natCard_orbit_eq_natDegree_factor`. -/
noncomputable def orbitQuotientEquivFactors [Normal F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) (hres : (spec.specialize F f).Separable) :
    MulAction.orbitRel.Quotient ((Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom)
        (Equiv.Perm (Fin n) ⧸ spec.H) ≃ (spec.specialize F f).Factors :=
  Equiv.ofBijective
    (Quotient.lift
      (fun c => (⟨minpoly F (cosetValue spec e c), by
          have hint : IsIntegral F (cosetValue spec e c) := Algebra.IsIntegral.isIntegral _
          exact ⟨minpoly.irreducible hint, minpoly.monic hint,
            minpoly.dvd F _ (aeval_cosetValue spec hf hsep hdeg e c)⟩⟩ :
            (spec.specialize F f).Factors))
      fun _ _ hcd => Subtype.ext ((minpoly_cosetValue_eq_iff spec hf hsep hdeg e hres).2 hcd))
    ⟨by
      refine fun a b => Quotient.inductionOn₂ a b fun c d hcd => Quotient.sound ?_
      exact (minpoly_cosetValue_eq_iff spec hf hsep hdeg e hres).1 (Subtype.ext_iff.1 hcd), by
      intro q
      obtain ⟨c, hc⟩ := exists_minpoly_cosetValue_eq spec hf hsep hdeg e q
      exact ⟨Quotient.mk _ c, Subtype.ext hc⟩⟩

-- The factorization equivalence on the orbit of a coset, through the value of that coset.
private theorem coe_orbitQuotientEquivFactors_mk [Normal F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) (hres : (spec.specialize F f).Separable)
    (c : Equiv.Perm (Fin n) ⧸ spec.H) :
    ((spec.orbitQuotientEquivFactors hf hsep hdeg e hres (Quotient.mk _ c) :
        (spec.specialize F f).Factors) : F[X]) = minpoly F (cosetValue spec e c) :=
  (rfl)

/-- The factorization equivalence sends the orbit of the coset of `τ` to the minimal polynomial
of the value at the roots of `f` of the invariant renamed along `τ`. -/
@[simp]
theorem orbitQuotientEquivFactors_apply_mk [Normal F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) (hres : (spec.specialize F f).Separable)
    (τ : Equiv.Perm (Fin n)) :
    ((spec.orbitQuotientEquivFactors hf hsep hdeg e hres
        (Quotient.mk _ (τ : Equiv.Perm (Fin n) ⧸ spec.H)) : (spec.specialize F f).Factors) : F[X])
      = minpoly F (MvPolynomial.eval₂ (Int.castRingHom E) (fun i => ((e.symm i : f.rootSet E) : E))
          (MvPolynomial.rename ⇑τ spec.Φ)) :=
  (rfl)

/-- A factor corresponds to the orbit of the coset of `τ` exactly when it is the minimal
polynomial of the value at the roots of `f` of the invariant renamed along `τ`. -/
@[simp]
theorem orbitQuotientEquivFactors_symm_apply_eq_mk_iff [Normal F E] (hf : f.Monic)
    (hsep : f.Separable) (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n)
    (hres : (spec.specialize F f).Separable) (q : (spec.specialize F f).Factors)
    (τ : Equiv.Perm (Fin n)) :
    (spec.orbitQuotientEquivFactors hf hsep hdeg e hres).symm q
        = Quotient.mk _ (τ : Equiv.Perm (Fin n) ⧸ spec.H) ↔
      (q : F[X]) = minpoly F (MvPolynomial.eval₂ (Int.castRingHom E)
        (fun i => ((e.symm i : f.rootSet E) : E)) (MvPolynomial.rename ⇑τ spec.Φ)) := by
  rw [Equiv.symm_apply_eq, Subtype.ext_iff, orbitQuotientEquivFactors_apply_mk]

/-- **Factor degrees are orbit sizes.** Along `TauCeti.ResolventSpec.orbitQuotientEquivFactors`,
the size of an orbit of the Galois image on the cosets of `H` is the degree of the matching monic
irreducible factor of the separable resolvent. -/
theorem natCard_orbit_eq_natDegree_factor [Normal F E] (hf : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n) (hres : (spec.specialize F f).Separable)
    (ω : MulAction.orbitRel.Quotient
      ((Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom)
      (Equiv.Perm (Fin n) ⧸ spec.H)) :
    Nat.card (MulAction.orbitRel.Quotient.orbit ω)
      = ((spec.orbitQuotientEquivFactors hf hsep hdeg e hres ω : (spec.specialize F f).Factors) :
          F[X]).natDegree := by
  induction ω using Quotient.inductionOn with | h c => ?_
  have hint : IsIntegral F (cosetValue spec e c) := Algebra.IsIntegral.isIntegral _
  have hqsep : (minpoly F (cosetValue spec e c)).Separable :=
    hres.of_dvd (minpoly.dvd F _ (aeval_cosetValue spec hf hsep hdeg e c))
  have hsplits : ((minpoly F (cosetValue spec e c)).map (algebraMap F E)).Splits :=
    Normal.splits' _
  rw [MulAction.orbitRel.Quotient.orbit_mk,
    ← Nat.card_image_of_injective (cosetValue_injective spec hf hsep hdeg e hres),
    image_cosetValue_orbit spec hf hsep hdeg e hres, Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree hqsep hsplits, coe_orbitQuotientEquivFactors_mk]

open scoped Classical in
/-- **The factor degrees of a separable resolvent are the orbit sizes.** Under the hypotheses of
`TauCeti.ResolventSpec.orbitQuotientEquivFactors`, the multiset of degrees of the monic irreducible
factors of the resolvent is the multiset of sizes of the orbits of the Galois image on the cosets
of `H`. -/
theorem map_natDegree_normalizedFactors_specialize [Normal F E] (hf : f.Monic)
    (hsep : f.Separable) (hdeg : f.natDegree = n) (e : f.rootSet E ≃ Fin n)
    (hres : (spec.specialize F f).Separable) :
    (UniqueFactorizationMonoid.normalizedFactors (spec.specialize F f)).map natDegree
      = Finset.univ.val.map fun ω : MulAction.orbitRel.Quotient
          ((Gal.galActionHom f E).range.map e.permCongrHom.toMonoidHom)
          (Equiv.Perm (Fin n) ⧸ spec.H) => Nat.card (MulAction.orbitRel.Quotient.orbit ω) := by
  have hg0 : spec.specialize F f ≠ 0 := (spec.monic_specialize F f).ne_zero
  have := Factors.finite hg0
  have := Fintype.ofFinite (spec.specialize F f).Factors
  -- A separable polynomial has each monic irreducible factor exactly once.
  have hnf : UniqueFactorizationMonoid.normalizedFactors (spec.specialize F f)
      = Finset.univ.val.map (Subtype.val : (spec.specialize F f).Factors → F[X]) := by
    refine (Multiset.Nodup.ext
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hg0).1 hres.squarefree)
      (Finset.univ.nodup.map Subtype.val_injective)).2 fun p => ?_
    rw [Polynomial.mem_normalizedFactors_iff hg0, Multiset.mem_map]
    exact ⟨fun hp => ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩, fun ⟨q, _, hq⟩ => hq ▸ q.2⟩
  rw [hnf, ← Finset.map_univ_equiv (spec.orbitQuotientEquivFactors hf hsep hdeg e hres),
    Finset.map_val, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun ω _ =>
    (spec.natCard_orbit_eq_natDegree_factor hf hsep hdeg e hres ω).symm

end ResolventSpec

end TauCeti
