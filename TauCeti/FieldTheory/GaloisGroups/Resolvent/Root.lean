/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Spec

import Mathlib.FieldTheory.Galois.Infinite
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Roots of a resolvent in the base field

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

## Main results

* `TauCeti.ResolventSpec.exists_isRoot_specialize_of_le` and
  `TauCeti.ResolventSpec.exists_isRoot_specialize_of_le_map_conj`: a Galois image inside `H`,
  respectively inside a conjugate of `H`, gives the resolvent a root in the base field.
* `TauCeti.ResolventSpec.exists_le_map_conj_of_isRoot_specialize`: conversely, when the
  specialized resolvent is separable, a root of it in the base field confines the Galois image to
  a conjugate of `H`.
* `TauCeti.ResolventSpec.exists_isRoot_specialize_iff_exists_le_map_conj`: the two together, the
  criterion that a separable resolvent provides.

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
  rw [show ((ϕ : E →+* E).comp (Int.castRingHom E)) = Int.castRingHom E from
    RingHom.ext_int _ _] at h
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

end ResolventSpec

end TauCeti
