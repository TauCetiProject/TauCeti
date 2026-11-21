/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.HilbertTower
import TauCeti.NumberTheory.NumberField.Global.Ideles.IdealExtension
import TauCeti.NumberTheory.NumberField.InfinitePlace.NormalClosure
import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
import TauCeti.RingTheory.ClassGroup.Extension
import TauCeti.RingTheory.Unramified.AlgEquiv

/-!
# The principal ideal theorem

Let `H` be the Hilbert class field of a number field `K`. Every ideal of `𝓞 K` becomes
principal in `𝓞 H` (`isPrincipal_map_hilbertClassField`); equivalently, extension of ideal
classes `Cl_K → Cl_H` is trivial (`extendedHom_hilbertClassField_eq_one`). On idele classes,
every idele class of `K`, extended to `H`, lies in the ray subgroup of the trivial modulus of `H`
(`ideleClassExtension_hilbertClassField_mem_raySubgroup_one`).

The proof is Artin's reduction of the theorem to Furtwängler's theorem on the transfer into the
commutator subgroup, read in the idele-class formation. Embed the Hilbert class field of `H`,
over `H`, into the separable closure `Kˢ` of `K`, and let `L` be the normal closure over `K` of
its image `X`. The extensions `X / H` and `H / K` are unramified at every finite and infinite place,
hence so are `X / K` and its normal closure `L / K`. So `L / K` is a finite Galois extension,
unramified everywhere and containing `H`, and the transfer theorem
`ideleClassExtension_mem_range_ideleClassNormMap_of_unramified` makes every idele class of `K`,
extended to `H`, a norm from `L`. Norms from `L` are norms from `X`, and the norm group of `X / H`
is the ray subgroup of the trivial modulus of `H`, because `X` is `H`-isomorphic to the Hilbert
class field of `H`. Reading idele classes as ideal classes
(`extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup`) gives the theorem.

Passing to the normal closure avoids showing that the Hilbert class field of `H` is itself
Galois over `K`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, Theorem 3.17.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §7.
-/

public section

open IntermediateField NumberField IsDedekindDomain

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

/-- An `F`-isomorphic copy of the Hilbert class field of `F` inside any separably closed
extension `Ω` of `F`. It is unramified over `F` at every finite and infinite place, and its
idele-class norm group is the ray subgroup of the trivial modulus. The statement is existential
so that it can be used for `F = hilbertClassField K` without naming the Hilbert class field of
`F` itself. -/
private theorem exists_range_ideleClassNormMap_eq_raySubgroup_one (F Ω : Type) [Field F]
    [NumberField F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω] :
    ∃ (X : IntermediateField F Ω) (_ : NumberField X),
      (∀ w : HeightOneSpectrum (𝓞 X), Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ∧
      IsUnramifiedAtInfinitePlaces F X ∧
      (ideleClassNormMap F X : IdeleClassGroup (𝓞 X) X →* IdeleClassGroup (𝓞 F) F).range =
        raySubgroup (Modulus.one F) := by
  let ψ : hilbertClassField F →ₐ[F] Ω :=
    (IsSepClosed.lift : SeparableClosure F →ₐ[F] Ω).comp (hilbertClassField F).val
  have : FiniteDimensional F ψ.fieldRange := ψ.equivFieldRange.toLinearEquiv.finiteDimensional
  have : NumberField ψ.fieldRange := NumberField.of_module_finite F _
  refine ⟨ψ.fieldRange, inferInstance, fun w ↦ ?_, ψ.isUnramifiedAtInfinitePlaces_fieldRange, ?_⟩
  · let e := RingOfIntegers.mapAlgEquiv (k := F) ψ.equivFieldRange
    have hw : w.asIdeal.comap e ≠ ⊥ := fun h ↦ w.ne_bot <| by
      rw [← Ideal.map_comap_of_surjective e e.surjective w.asIdeal, h, Ideal.map_bot]
    exact (e.isUnramifiedAt_iff_of_eq_comap
      (p := (⟨w.asIdeal.comap e, inferInstance, hw⟩ : HeightOneSpectrum _).asIdeal) rfl).1
      (isUnramifiedAt_hilbertClassField F _)
  · rw [← range_ideleClassNormMap_eq_of_algEquiv ψ.equivFieldRange]
    exact range_ideleClassNormMap_rayClassField _

variable {K : Type} [Field K] [NumberField K]

/-- If a finite Galois extension `L / K` inside `Kˢ`, unramified at every finite and infinite
place and containing the Hilbert class field `H`, receives an `H`-embedding of an extension `M`
of `H` whose norm group lies in the trivial-modulus ray subgroup, then every idele class of `K`,
extended to `H`, lies in that ray subgroup. -/
private theorem ideleClassExtension_mem_raySubgroup_one_of_algHom
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [IsGalois K L]
    [Algebra (hilbertClassField K) L] [IsScalarTower (hilbertClassField K) L (SeparableClosure K)]
    (hur : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K L] {M : Type} [Field M] [NumberField M]
    [Algebra (hilbertClassField K) M] (f : M →ₐ[hilbertClassField K] L)
    (hM : (ideleClassNormMap (hilbertClassField K) M :
        IdeleClassGroup (𝓞 M) M →* IdeleClassGroup (𝓞 _) _).range ≤
      raySubgroup (Modulus.one (hilbertClassField K)))
    (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      raySubgroup (Modulus.one (hilbertClassField K)) := by
  obtain ⟨V, rfl⟩ := (exists_classField_eq_iff L).2 ⟨inferInstance, inferInstance⟩
  exact hM (range_ideleClassNormMap_le_of_algHom f
    (ideleClassExtension_mem_range_ideleClassNormMap_of_unramified V hur c))

/-- **The principal ideal theorem, for idele classes.** Every idele class of `K`, extended to
the Hilbert class field `H` of `K`, lies in the ray subgroup of the trivial modulus of `H`, the
kernel of the quotient `C_H → Cl_H`. -/
theorem ideleClassExtension_hilbertClassField_mem_raySubgroup_one (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      raySubgroup (Modulus.one (hilbertClassField K)) := by
  -- `X` is a copy of the Hilbert class field of `H` in `Kˢ`, and `L` its normal closure over `K`.
  obtain ⟨X, _, hXur, _, hXnorm⟩ :=
    exists_range_ideleClassNormMap_eq_raySubgroup_one (hilbertClassField K) (SeparableClosure K)
  have : FiniteDimensional K X := Module.Finite.trans (hilbertClassField K) X
  let ι : X →ₐ[K] SeparableClosure K := X.val.restrictScalars K
  let L := normalClosure K X (SeparableClosure K)
  have : IsGalois K L := ⟨⟩
  have hXL (x) (hx : x ∈ X) : x ∈ L := ι.fieldRange_le_normalClosure ⟨⟨x, hx⟩, rfl⟩
  have hHL : hilbertClassField K ≤ L := fun x hx ↦ hXL x (X.algebraMap_mem ⟨x, hx⟩)
  let _ : Algebra (hilbertClassField K) L := (inclusion hHL).toAlgebra
  have : IsScalarTower (hilbertClassField K) L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- `X / K` is unramified at the finite places, as `X / H` and `H / K` are, and hence so is `L`.
  have hXK (p : Ideal (𝓞 K)) (hp : p ≠ ⊥) : Algebra.IsUnramifiedIn (𝓞 X) p := by
    intro P _ _
    have hq : P.under (𝓞 (hilbertClassField K)) ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot hp (P.under (𝓞 (hilbertClassField K)))
    have := isUnramifiedAt_hilbertClassField K ⟨_, inferInstance, hq⟩
    have := hXur ⟨P, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot hp P⟩
    exact Algebra.IsUnramifiedAt.comp (P.under (𝓞 (hilbertClassField K))) P
  have : Nonempty (X →ₐ[K] SeparableClosure K) := ⟨ι⟩
  have hur (w : HeightOneSpectrum (𝓞 L)) : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (Ideal.isUnramifiedIn_normalClosure_iff_of_normal _).2
      (hXK _ (Ideal.under_ne_bot (𝓞 K) w.ne_bot)) w.asIdeal inferInstance inferInstance
  -- At the infinite places, `X / K` is unramified as a tower, and hence so is its normal closure.
  have : IsUnramifiedAtInfinitePlaces K X := .trans K (hilbertClassField K) X
  -- The inclusion `X ⊆ L` over `H`; both algebra maps from `H` are the inclusions into `Kˢ`.
  let f : X →ₐ[hilbertClassField K] L :=
    { toRingHom := X.val.toRingHom.codRestrict L fun x ↦ hXL x x.2
      commutes' := fun _ ↦ rfl }
  exact ideleClassExtension_mem_raySubgroup_one_of_algHom L hur f hXnorm.le c

/-- **The principal ideal theorem, for ideal classes.** Extension of ideal classes from `K` to its
Hilbert class field is trivial. -/
theorem extendedHom_hilbertClassField_eq_one :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (hilbertClassField K)) = 1 :=
  extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup.2
    ideleClassExtension_hilbertClassField_mem_raySubgroup_one

/-- **The principal ideal theorem** (Artin–Furtwängler). Every ideal of the ring of integers of a
number field `K` becomes principal in the ring of integers of the Hilbert class field of `K`. -/
theorem isPrincipal_map_hilbertClassField (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (hilbertClassField K)))).IsPrincipal :=
  (ClassGroup.extendedHom_eq_one_iff_forall_isPrincipal _ _).1
    extendedHom_hilbertClassField_eq_one I

end TauCeti.ClassFieldTheory
