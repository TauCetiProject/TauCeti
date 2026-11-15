/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IdealExtension

/-!
# Ideal classes of extended ideles

Extension of ideles induces the usual extension of ideal classes. In particular, the
trivial-modulus ray-class quotient commutes with extension of scalars. Thus an idelic
principalization statement can be read as triviality of the extension map on ideal classes,
without choosing representatives or rebuilding the class-group map.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§1, 7.
-/

public section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Extension of idele classes induces extension of ideal classes.** The quotient on either
side is the trivial-modulus ray-class quotient, identified with the ordinary class group. -/
@[simp]
theorem oneEquivClassGroup_rayClassQuotient_ideleClassExtension
    (c : IdeleClassGroup (𝓞 K) K) :
    oneEquivClassGroup (rayClassQuotient (Modulus.one L) (ideleClassExtension K L c)) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (oneEquivClassGroup (rayClassQuotient (Modulus.one K) c)) := by
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [ideleClassExtension_mk, oneEquivClassGroup_rayClassQuotient_mk,
      oneEquivClassGroup_rayClassQuotient_mk, toFiniteIdele_ideleExtension]
    exact FiniteAdeleRing.toClassGroup_unitsMap_finiteAdeleExtension
      (K := K) (L := L) (IdeleGroup.toFiniteIdele (𝓞 K) K x)

/-- **Idelic criterion for principalization of ideal classes.** Extension kills every ideal
class exactly when every extended idele class lies in the trivial-modulus ray subgroup. -/
theorem extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup :
    ClassGroup.extendedHom (𝓞 K) (𝓞 L) = 1 ↔
      ∀ c : IdeleClassGroup (𝓞 K) K,
        ideleClassExtension K L c ∈ raySubgroup (Modulus.one L) := by
  have hmem (c : IdeleClassGroup (𝓞 K) K) :
      ideleClassExtension K L c ∈ raySubgroup (Modulus.one L) ↔
        ClassGroup.extendedHom (𝓞 K) (𝓞 L)
          (oneEquivClassGroup (rayClassQuotient (Modulus.one K) c)) = 1 := by
    rw [← ker_rayClassQuotient, MonoidHom.mem_ker,
      ← (oneEquivClassGroup (K := L)).map_eq_one_iff,
      oneEquivClassGroup_rayClassQuotient_ideleClassExtension]
  simp_rw [hmem]
  constructor
  · intro h c
    simp [h]
  · intro h
    ext a
    obtain ⟨c, rfl⟩ := (oneEquivClassGroup (K := K)).surjective.comp
      (rayClassQuotient_surjective (Modulus.one K)) a
    exact h c

end TauCeti.GlobalNumberFields
