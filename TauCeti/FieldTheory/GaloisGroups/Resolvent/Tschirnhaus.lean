/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Label
public import TauCeti.FieldTheory.GaloisGroups.Tschirnhaus

/-!
# Resolvents of a Tschirnhaus transform

A resolvent specialized at a monic separable polynomial `f` detects the Galois image of `f` only
when it is separable: two values of the orbit of the invariant that collide at the roots of `f`
give the resolvent a root in the base field that constrains the Galois image no further. The
classical remedy replaces `f` by an admissible Tschirnhaus transform
`Polynomial.tschirnhausPolynomial f T`, whose roots are the values `T(α)` at the roots `α` of `f`,
and computes the resolvent of the transform instead.

This file shows that the remedy is sound. An admissible transform of a monic separable `f` is
again monic and separable of the same degree, and, when its roots are numbered through
`α ↦ T(α)`, its Galois image is the Galois image of `f`
(`Polynomial.TschirnhausAdmissible.map_range_galActionHom_tschirnhausPolynomial`). The resolvent
criterion and the factorization theorem applied to the transform are therefore statements about
`f`. In particular, if the resolvent of the transform is separable and has a root in the base
field, then the Galois image of `f` lies in a conjugate of the subgroup of the specification.
Separability of the resolvent of the transform is the only extra condition: like every
specialization, it is monic of the full orbit degree.

## Main results

* `TauCeti.ResolventSpec.exists_le_map_conj_of_isRoot_specialize_tschirnhausPolynomial`: a root of
  the separable resolvent of an admissible transform confines the Galois image of `f` to a
  conjugate of `H`.
* `TauCeti.ResolventSpec.exists_isRoot_specialize_tschirnhausPolynomial_of_le_map_conj`:
  conversely, without any hypothesis on the resolvent, a Galois image of `f` inside a conjugate of
  `H` gives the resolvent of every admissible transform a root.
* `TauCeti.ResolventSpec.exists_isRoot_specialize_tschirnhausPolynomial_iff_exists_le_map_conj`:
  the resolvent criterion, applied through an admissible transform.
* `TauCeti.ResolventSpec.map_natDegree_normalizedFactors_specialize_tschirnhausPolynomial`: the
  factor degrees of the separable resolvent of an admissible transform are the sizes of the orbits
  of the Galois image of `f` on the cosets of `H`.
* `TauCeti.HasGaloisLabel.exists_isRoot_specialize_tschirnhausPolynomial_of_exists_le_map_conj`
  and `TauCeti.HasGaloisLabel.exists_isRoot_specialize_tschirnhausPolynomial_iff`: the two
  directions read on the transitive-group label of `f`.

## References

* [H. Cohen, *A Course in Computational Algebraic Number Theory*][cohen1993], §6.3.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F] {f T : F[X]} {n : ℕ}

namespace ResolventSpec

variable {E : Type*} [Field E] [Algebra F E] [hfsp : Fact ((f.map (algebraMap F E)).Splits)]
  (spec : ResolventSpec n)

/-- **A root of the separable resolvent of an admissible transform confines the Galois image.**
Let `f` be monic and separable of degree `n`, let `E` be a normal splitting extension, number the
roots of `f` in `E` by `e`, and let `T` be admissible for `f`. If the resolvent of the Tschirnhaus
transform of `f` by `T` is separable and has a root in `F`, then the Galois image of `f`, read
through `e`, lies in a conjugate of the subgroup of the specification.

The resolvent of `f` itself may be inseparable here; this is the case the transform is for. -/
theorem exists_le_map_conj_of_isRoot_specialize_tschirnhausPolynomial [Normal F E]
    (hf : f.Monic) (hsep : f.Separable) (hdeg : f.natDegree = n)
    (hT : TschirnhausAdmissible f T) (e : f.rootSet E ≃ Fin n)
    (hres : (spec.specialize F (f.tschirnhausPolynomial T)).Separable) {a : F}
    (ha : (spec.specialize F (f.tschirnhausPolynomial T)).IsRoot a) :
    ∃ τ : Equiv.Perm (Fin n),
      (Gal.galActionHom f E).range.map
        (e.permCongrHom : _ →* Equiv.Perm (Fin n))
        ≤ spec.H.map (MulAut.conj τ).toMonoidHom := by
  have : Fact (((f.tschirnhausPolynomial T).map (algebraMap F E)).Splits) :=
    ⟨splits_map_tschirnhausPolynomial_field hfsp.out T⟩
  rw [← hT.map_range_galActionHom_tschirnhausPolynomial hsep.ne_zero e]
  exact spec.exists_le_map_conj_of_isRoot_specialize (monic_tschirnhausPolynomial hf T)
    ((separable_tschirnhausPolynomial_iff hsep.ne_zero T).2 ⟨hsep, hT⟩)
    ((natDegree_tschirnhausPolynomial hf T).trans hdeg) _ hres ha

/-- **A Galois image inside a conjugate of `H` gives the resolvent of every admissible transform a
root.** Let `f` be monic and separable of degree `n`, let `E` be a Galois splitting extension, and
number the roots of `f` in `E` by `e`. If the Galois image of `f`, read through `e`, lies in a
conjugate of the subgroup of the specification, then for every admissible `T` the resolvent of the
Tschirnhaus transform of `f` by `T` has a root in `F`. Nothing is assumed about that resolvent. -/
theorem exists_isRoot_specialize_tschirnhausPolynomial_of_le_map_conj [IsGalois F E]
    (hf : f.Monic) (hsep : f.Separable) (hdeg : f.natDegree = n)
    (hT : TschirnhausAdmissible f T) (e : f.rootSet E ≃ Fin n) (τ : Equiv.Perm (Fin n))
    (hle : (Gal.galActionHom f E).range.map
      (e.permCongrHom : _ →* Equiv.Perm (Fin n))
      ≤ spec.H.map (MulAut.conj τ).toMonoidHom) :
    ∃ a : F, (spec.specialize F (f.tschirnhausPolynomial T)).IsRoot a := by
  have : Fact (((f.tschirnhausPolynomial T).map (algebraMap F E)).Splits) :=
    ⟨splits_map_tschirnhausPolynomial_field hfsp.out T⟩
  rw [← hT.map_range_galActionHom_tschirnhausPolynomial hsep.ne_zero e] at hle
  exact spec.exists_isRoot_specialize_of_le_map_conj (monic_tschirnhausPolynomial hf T)
    ((separable_tschirnhausPolynomial_iff hsep.ne_zero T).2 ⟨hsep, hT⟩)
    ((natDegree_tschirnhausPolynomial hf T).trans hdeg) _ τ hle

/-- **The resolvent criterion through an admissible transform.** Let `f` be monic and separable
of degree `n`, let `E` be a Galois splitting extension, number the roots of `f` in `E` by `e`, and
let `T` be admissible for `f`. If the resolvent of the Tschirnhaus transform of `f` by `T` is
separable, it has a root in `F` exactly when the Galois image of `f`, read through `e`, lies in a
conjugate of the subgroup of the specification. -/
theorem exists_isRoot_specialize_tschirnhausPolynomial_iff_exists_le_map_conj [IsGalois F E]
    (hf : f.Monic) (hsep : f.Separable) (hdeg : f.natDegree = n)
    (hT : TschirnhausAdmissible f T) (e : f.rootSet E ≃ Fin n)
    (hres : (spec.specialize F (f.tschirnhausPolynomial T)).Separable) :
    (∃ a : F, (spec.specialize F (f.tschirnhausPolynomial T)).IsRoot a) ↔
      ∃ τ : Equiv.Perm (Fin n),
        (Gal.galActionHom f E).range.map
          (e.permCongrHom : _ →* Equiv.Perm (Fin n))
          ≤ spec.H.map (MulAut.conj τ).toMonoidHom :=
  ⟨fun ⟨_, ha⟩ ↦ spec.exists_le_map_conj_of_isRoot_specialize_tschirnhausPolynomial
      hf hsep hdeg hT e hres ha,
    fun ⟨τ, hτ⟩ ↦ spec.exists_isRoot_specialize_tschirnhausPolynomial_of_le_map_conj
      hf hsep hdeg hT e τ hτ⟩

open scoped Classical in
/-- **The factor degrees of the separable resolvent of an admissible transform are orbit sizes.**
Let `f` be monic and separable of degree `n`, let `E` be a normal splitting extension, number the
roots of `f` in `E` by `e`, and let `T` be admissible for `f`. If the resolvent of the
Tschirnhaus transform of `f` by `T` is separable, the multiset of degrees of its monic irreducible
factors is the multiset of sizes of the orbits of the Galois image of `f`, read through `e`, on
the cosets of `H`. -/
theorem map_natDegree_normalizedFactors_specialize_tschirnhausPolynomial [Normal F E]
    (hf : f.Monic) (hsep : f.Separable) (hdeg : f.natDegree = n)
    (hT : TschirnhausAdmissible f T) (e : f.rootSet E ≃ Fin n)
    (hres : (spec.specialize F (f.tschirnhausPolynomial T)).Separable) :
    (UniqueFactorizationMonoid.normalizedFactors
        (spec.specialize F (f.tschirnhausPolynomial T))).map natDegree
      = Finset.univ.val.map fun ω : MulAction.orbitRel.Quotient
          ((Gal.galActionHom f E).range.map
            (e.permCongrHom : _ →* Equiv.Perm (Fin n)))
          (Equiv.Perm (Fin n) ⧸ spec.H) => Nat.card (MulAction.orbitRel.Quotient.orbit ω) := by
  have : Fact (((f.tschirnhausPolynomial T).map (algebraMap F E)).Splits) :=
    ⟨splits_map_tschirnhausPolynomial_field hfsp.out T⟩
  have h := spec.map_natDegree_normalizedFactors_specialize (monic_tschirnhausPolynomial hf T)
    ((natDegree_tschirnhausPolynomial hf T).trans hdeg)
    ((hT.rootSetEquiv hsep.ne_zero hfsp.out).symm.trans e) hres
  rwa [hT.map_range_galActionHom_tschirnhausPolynomial hsep.ne_zero e] at h

end ResolventSpec

-- The `Fact` that `Polynomial.Gal.galActionHom` asks for, kept local as in
-- `TauCeti.FieldTheory.GaloisGroups.Label`.
attribute [local instance] factSplitsSplittingField

variable {j : TransitiveGroupIndex n}

/-- **A label confined to the subgroup of a specification gives the resolvent of every admissible
transform a root.** If the reference subgroup of the label of a monic `f` lies in a conjugate of
the subgroup of a resolvent specification, then for every admissible `T` the resolvent of the
Tschirnhaus transform of `f` by `T` has a root in the base field. Nothing is assumed about that
resolvent. -/
theorem HasGaloisLabel.exists_isRoot_specialize_tschirnhausPolynomial_of_exists_le_map_conj
    (h : HasGaloisLabel f j) (hf : f.Monic) (hT : TschirnhausAdmissible f T)
    (spec : ResolventSpec n)
    (hle : ∃ τ : Equiv.Perm (Fin n),
      referenceSubgroup n j ≤ spec.H.map (MulAut.conj τ).toMonoidHom) :
    ∃ a : F, (spec.specialize F (f.tschirnhausPolynomial T)).IsRoot a := by
  have : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field h.separable
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f h.separable
  obtain ⟨τ, hτ⟩ :=
    (h.transitiveGroupLabel (e.trans (finCongr h.natDegree_eq))).exists_le_map_conj_iff.2 hle
  exact spec.exists_isRoot_specialize_tschirnhausPolynomial_of_le_map_conj hf h.separable
    h.natDegree_eq hT _ τ hτ

/-- **The resolvent criterion through an admissible transform, read on the label.** Let `f` be
monic with a transitive-group label and let `T` be admissible for `f`. If the resolvent of the
Tschirnhaus transform of `f` by `T` is separable, it has a root in the base field exactly when the
reference subgroup of the label of `f` lies in a conjugate of the subgroup of the specification.

Separability of the resolvent of the transform is what the forward implication needs; the reverse
implication is
`TauCeti.HasGaloisLabel.exists_isRoot_specialize_tschirnhausPolynomial_of_exists_le_map_conj`. -/
theorem HasGaloisLabel.exists_isRoot_specialize_tschirnhausPolynomial_iff
    (h : HasGaloisLabel f j) (hf : f.Monic) (hT : TschirnhausAdmissible f T)
    (spec : ResolventSpec n)
    (hres : (spec.specialize F (f.tschirnhausPolynomial T)).Separable) :
    (∃ a : F, (spec.specialize F (f.tschirnhausPolynomial T)).IsRoot a) ↔
      ∃ τ : Equiv.Perm (Fin n), referenceSubgroup n j ≤ spec.H.map (MulAut.conj τ).toMonoidHom := by
  have : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field h.separable
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f h.separable
  rw [spec.exists_isRoot_specialize_tschirnhausPolynomial_iff_exists_le_map_conj hf h.separable
    h.natDegree_eq hT (e.trans (finCongr h.natDegree_eq)) hres]
  exact (h.transitiveGroupLabel _).exists_le_map_conj_iff

end TauCeti
