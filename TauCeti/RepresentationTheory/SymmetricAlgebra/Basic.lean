/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Invariant.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear

/-!
# The induced action on a symmetric algebra and its invariant subalgebra

A representation `ρ` of a monoid `G` on a module `M` extends multiplicatively to the symmetric
algebra `Sym M`: each `ρ g` induces the algebra endomorphism `SymmetricAlgebra.map (ρ g)`. Taking
`M = V*` with the contragredient representation `Representation.dual` gives the action of `G` on
polynomial functions on `V`, the starting point of the invariant theory of finite linear groups.

The induced action preserves the grading of `Sym M` by homogeneous degree. Its fixed points form a
subalgebra, the *invariant subalgebra* `Sym(M)^G`, which is homogeneous: every homogeneous
component of an invariant is again invariant. Restricting the action to a homogeneous
component `Symⁿ M` gives a representation whose invariants are the degree-`n` part of
`Sym(M)^G`; these are the pieces whose dimensions form the Hilbert series of the invariant
subalgebra. In degree one the invariants are exactly the invariant vectors of `M`. For a finite
group `G`, `Sym M` is integral over its invariants: an element `p` is a root of the monic
polynomial `∏ g, (X - g • p)`, whose coefficients are invariant
(`Algebra.IsInvariant.isIntegral`).

Each `ρ g` fixes the invariant subalgebra pointwise, so it is linear over it; this gives the
representation `Representation.symmetricAlgebraOverInvariants` of `G` on `Sym M` as a module over
`Sym(M)^G`, whose invariants are `Sym(M)^G` itself.

Since the representation `ρ` is data that instance search cannot infer, the induced action is
bundled as `Representation.symmetricAlgebraMulSemiringAction` for local use, rather than
registered as an instance; this gives access to the `MulSemiringAction` API, in particular to
Mathlib's invariant extensions `Algebra.IsInvariant`.

## Main definitions

* `Representation.symmetricAlgebra`: the representation of `G` on `Sym M` induced by `ρ`.
* `Representation.symmetricAlgebraMulSemiringAction`: the same action, bundled as an action by
  semiring endomorphisms.
* `Representation.symmetricAlgebraInvariants`: the subalgebra of `Sym M` fixed by every `ρ g`.
* `Representation.symmetricAlgebraOverInvariants`: the induced action on `Sym M`, as a
  representation by linear maps over the invariant subalgebra.
* `Representation.symmetricAlgebraHomogeneous`: the representation of `G` on the degree-`n`
  homogeneous component `Symⁿ M`.

## Main results

* `Representation.symmetricAlgebra_mem_homogeneousSubmodule` and
  `Representation.decompose_symmetricAlgebra`: the induced action preserves degrees and commutes
  with taking homogeneous components.
* `Representation.isHomogeneous_symmetricAlgebraInvariants`: the invariant subalgebra is a
  homogeneous subalgebra.
* `Representation.toSubmodule_symmetricAlgebraInvariants`: as a submodule, it is the module of
  invariants of the induced representation.
* `Representation.ι_mem_symmetricAlgebraInvariants_iff`: its degree-one part is `M^G`.
* `Representation.mem_invariants_symmetricAlgebraOverInvariants_iff`: the invariants of the
  action over the invariant subalgebra are the invariant subalgebra.
* `Representation.symmetricAlgebraHomogeneous_apply`: on `Symⁿ M`, `g` acts by the map
  `homogeneousSubmoduleMapₛₗ (ρ g) n` induced on degree `n`.
* `Representation.map_subtype_invariants_symmetricAlgebraHomogeneous` and
  `Representation.finrank_invariants_symmetricAlgebraHomogeneous`: the invariants of `Symⁿ M` are
  the degree-`n` part of the invariant subalgebra.
* `Representation.symmetricAlgebraInvariants_eq_fixedPoints` and
  `Representation.isInvariant_symmetricAlgebraInvariants`: it is the fixed subalgebra of the
  bundled action, and `Sym M` is an invariant extension of it in the sense of
  `Algebra.IsInvariant`.
* `Representation.isIntegral_symmetricAlgebraInvariants`: for a finite group, `Sym M` is integral
  over the invariant subalgebra.

## References

* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapters 1 and 2.
* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), 475–511.
* The construction of `Representation.symmetricAlgebra` follows the template of
  `Representation.symmetricPower` in `TauCeti.RepresentationTheory.SymmetricPower`.
-/

public section

open TauCeti.SymmetricAlgebra

namespace Representation

variable {R G M : Type*}

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M)

/-- The representation of `G` on the symmetric algebra `Sym M` induced by a representation `ρ`
on `M`: the element `g` acts by the algebra endomorphism extending `ρ g` multiplicatively.

For the contragredient representation `ρ.dual`, this is the action on polynomial functions. -/
noncomputable def symmetricAlgebra : Representation R G (SymmetricAlgebra R M) where
  toFun g := (SymmetricAlgebra.map R (ρ g)).toLinearMap
  map_one' := by
    rw [ρ.map_one, Module.End.one_eq_id, SymmetricAlgebra.map_id, Module.End.one_eq_id,
      AlgHom.toLinearMap_id]
  map_mul' g h := by
    rw [ρ.map_mul, Module.End.mul_eq_comp, ← SymmetricAlgebra.map_comp_map, AlgHom.comp_toLinearMap,
      Module.End.mul_eq_comp]

/-- The induced action of `g` is the symmetric-algebra map induced by `ρ g`. -/
@[simp]
theorem symmetricAlgebra_apply (g : G) (p : SymmetricAlgebra R M) :
    ρ.symmetricAlgebra g p = SymmetricAlgebra.map R (ρ g) p :=
  (rfl)

/-- The induced action applies `ρ` to a canonical generator.

This is intentionally not a simp lemma: `symmetricAlgebra_apply` followed by
`SymmetricAlgebra.map_apply_ι` already performs this simplification. -/
theorem symmetricAlgebra_ι (g : G) (m : M) :
    ρ.symmetricAlgebra g (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R M (ρ g m) := by
  rw [symmetricAlgebra_apply, SymmetricAlgebra.map_apply_ι]

/-- The induced action preserves every homogeneous degree. -/
theorem symmetricAlgebra_mem_homogeneousSubmodule (g : G) {n : ℕ} {p : SymmetricAlgebra R M}
    (hp : p ∈ homogeneousSubmodule R M n) :
    ρ.symmetricAlgebra g p ∈ homogeneousSubmodule R M n :=
  map_mem_homogeneousSubmodule (ρ g) hp

/-- The representation of `G` on the degree-`n` homogeneous component `Symⁿ M` of the symmetric
algebra: the restriction of `Representation.symmetricAlgebra` to this subrepresentation. -/
noncomputable def symmetricAlgebraHomogeneous (n : ℕ) :
    Representation R G (homogeneousSubmodule R M n) :=
  Subrepresentation.toRepresentation
    ⟨homogeneousSubmodule R M n, fun g _ ↦ ρ.symmetricAlgebra_mem_homogeneousSubmodule g⟩

/-- The action on `Symⁿ M` is computed in the symmetric algebra by the induced action. -/
@[simp]
theorem coe_symmetricAlgebraHomogeneous_apply (n : ℕ) (g : G)
    (p : homogeneousSubmodule R M n) :
    (ρ.symmetricAlgebraHomogeneous n g p : SymmetricAlgebra R M) = ρ.symmetricAlgebra g p :=
  (rfl)

/-- The action of `g` on `Symⁿ M` is the map `homogeneousSubmoduleMapₛₗ (ρ g) n` induced by
`ρ g` on degree `n`. -/
theorem symmetricAlgebraHomogeneous_apply (n : ℕ) (g : G) :
    ρ.symmetricAlgebraHomogeneous n g = homogeneousSubmoduleMapₛₗ (ρ g) n :=
  LinearMap.ext fun p ↦ Subtype.ext <| by
    rw [coe_symmetricAlgebraHomogeneous_apply, coe_homogeneousSubmoduleMapₛₗ_apply,
      SymmetricAlgebra.mapₛₗ_eq_map, symmetricAlgebra_apply, AlgHom.coe_toRingHom]

/-- The induced action commutes with taking homogeneous components. -/
theorem decompose_symmetricAlgebra (g : G) (p : SymmetricAlgebra R M) (n : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule R M) (ρ.symmetricAlgebra g p) n :
        SymmetricAlgebra R M) =
      ρ.symmetricAlgebra g (DirectSum.decompose (homogeneousSubmodule R M) p n) := by
  simpa only [SymmetricAlgebra.gradedMap_apply, symmetricAlgebra_apply] using
    ((SymmetricAlgebra.gradedMap R (ρ g)).map_directSumDecompose (x := p) (i := n)).symm

/-- The action of `G` on `Sym M` induced by `ρ`, bundled as an action by semiring
endomorphisms, for use with the API of `MulSemiringAction` (fixed points, orbit polynomials).
It is not an instance, since `ρ` cannot be inferred. -/
noncomputable abbrev symmetricAlgebraMulSemiringAction :
    MulSemiringAction G (SymmetricAlgebra R M) where
  smul g p := ρ.symmetricAlgebra g p
  one_smul := LinearMap.congr_fun (map_one ρ.symmetricAlgebra)
  mul_smul g h := LinearMap.congr_fun (map_mul ρ.symmetricAlgebra g h)
  smul_zero g := map_zero (ρ.symmetricAlgebra g)
  smul_add g := map_add (ρ.symmetricAlgebra g)
  smul_one g := (ρ.symmetricAlgebra_apply g 1).trans (map_one _)
  smul_mul g p q := (ρ.symmetricAlgebra_apply g (p * q)).trans <| (map_mul _ p q).trans <|
    congrArg₂ (· * ·) (ρ.symmetricAlgebra_apply g p).symm (ρ.symmetricAlgebra_apply g q).symm

/-- The bundled action is the induced representation. -/
theorem symmetricAlgebraMulSemiringAction_smul (g : G) (p : SymmetricAlgebra R M) :
    letI := ρ.symmetricAlgebraMulSemiringAction
    g • p = ρ.symmetricAlgebra g p :=
  (rfl)

/-- The bundled action commutes with scalar multiplication by `R`. -/
theorem smulCommClass_symmetricAlgebraMulSemiringAction :
    letI := ρ.symmetricAlgebraMulSemiringAction
    SMulCommClass G R (SymmetricAlgebra R M) :=
  letI := ρ.symmetricAlgebraMulSemiringAction
  ⟨fun g r p ↦ map_smul (ρ.symmetricAlgebra g) r p⟩

/-- The invariant subalgebra `Sym(M)^G`: the elements of `Sym M` fixed by the induced action of
every element of `G`, that is, the fixed subalgebra `FixedPoints.subalgebra` of the bundled
action. -/
noncomputable def symmetricAlgebraInvariants : Subalgebra R (SymmetricAlgebra R M) :=
  letI := ρ.symmetricAlgebraMulSemiringAction
  haveI := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
  FixedPoints.subalgebra R (SymmetricAlgebra R M) G

/-- An element of `Sym M` is invariant when every `g` fixes it. -/
@[simp]
theorem mem_symmetricAlgebraInvariants (p : SymmetricAlgebra R M) :
    p ∈ ρ.symmetricAlgebraInvariants ↔ ∀ g : G, ρ.symmetricAlgebra g p = p :=
  Iff.rfl

/-- The invariant subalgebra is the fixed subalgebra `FixedPoints.subalgebra` of the bundled
action `Representation.symmetricAlgebraMulSemiringAction`; this holds by definition. -/
theorem symmetricAlgebraInvariants_eq_fixedPoints :
    letI := ρ.symmetricAlgebraMulSemiringAction
    haveI := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
    ρ.symmetricAlgebraInvariants = FixedPoints.subalgebra R (SymmetricAlgebra R M) G :=
  (rfl)

/-- The invariant subalgebra is homogeneous: every homogeneous component of an invariant is
invariant. -/
theorem isHomogeneous_symmetricAlgebraInvariants :
    DirectSum.SetLike.IsHomogeneous (homogeneousSubmodule R M) ρ.symmetricAlgebraInvariants := by
  intro n p hp
  refine (ρ.mem_symmetricAlgebraInvariants _).2 fun g ↦ ?_
  rw [← decompose_symmetricAlgebra, (ρ.mem_symmetricAlgebraInvariants p).1 hp g]

/-- A degree-one element `ι m` is invariant exactly when `m` is a fixed vector of `ρ`. -/
theorem ι_mem_symmetricAlgebraInvariants_iff (m : M) :
    SymmetricAlgebra.ι R M m ∈ ρ.symmetricAlgebraInvariants ↔ ∀ g : G, ρ g m = m := by
  simp only [mem_symmetricAlgebraInvariants, symmetricAlgebra_ι,
    (ι_injective R M).eq_iff]

/-- The action of `G` on `Sym M` induced by `ρ`, as a representation by linear maps over the
invariant subalgebra `Sym(M)^G`: each `ρ g` fixes the invariants, so it is linear over them. Its
underlying maps are those of `Representation.symmetricAlgebra`. -/
noncomputable def symmetricAlgebraOverInvariants :
    Representation ρ.symmetricAlgebraInvariants G (SymmetricAlgebra R M) where
  toFun g :=
    { toFun := ρ.symmetricAlgebra g
      map_add' := map_add _
      map_smul' a p := by
        -- `g` fixes the invariant factor `a`.
        have ha := (ρ.mem_symmetricAlgebraInvariants a).1 a.2 g
        simp only [symmetricAlgebra_apply] at ha ⊢
        simp only [Subalgebra.smul_def, smul_eq_mul, map_mul, ha, RingHom.id_apply] }
  map_one' := LinearMap.ext fun p ↦ by simp
  map_mul' g h := LinearMap.ext fun p ↦ by simp

/-- Over the invariant subalgebra, `g` acts on `Sym M` by `Representation.symmetricAlgebra`. -/
@[simp]
theorem symmetricAlgebraOverInvariants_apply (g : G) (p : SymmetricAlgebra R M) :
    ρ.symmetricAlgebraOverInvariants g p = ρ.symmetricAlgebra g p :=
  (rfl)

end CommSemiring

section Group

variable [CommSemiring R] [Group G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M)

/-- For a group, `Sym M` is an invariant extension of the invariant subalgebra under the bundled
action, so Mathlib's `Algebra.IsInvariant` API applies to it. This is Mathlib's instance for
`FixedPoints.subalgebra`, transported along `symmetricAlgebraInvariants_eq_fixedPoints`. -/
theorem isInvariant_symmetricAlgebraInvariants :
    letI := ρ.symmetricAlgebraMulSemiringAction
    Algebra.IsInvariant ρ.symmetricAlgebraInvariants (SymmetricAlgebra R M) G :=
  letI := ρ.symmetricAlgebraMulSemiringAction
  haveI := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
  ρ.symmetricAlgebraInvariants_eq_fixedPoints ▸ inferInstance

end Group

section CommRing

variable [CommRing R] [Group G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M)

/-- As a submodule, the invariant subalgebra is the module of invariants of the induced
representation on `Sym M`. -/
@[simp]
theorem toSubmodule_symmetricAlgebraInvariants :
    Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants = ρ.symmetricAlgebra.invariants :=
  Submodule.ext fun p ↦
    (ρ.mem_symmetricAlgebraInvariants p).trans (ρ.symmetricAlgebra.mem_invariants p).symm

/-- An element of `Symⁿ M` is an invariant of the degree-`n` representation exactly when it lies
in the invariant subalgebra. -/
theorem mem_invariants_symmetricAlgebraHomogeneous_iff {n : ℕ} (p : homogeneousSubmodule R M n) :
    p ∈ (ρ.symmetricAlgebraHomogeneous n).invariants ↔
      (p : SymmetricAlgebra R M) ∈ ρ.symmetricAlgebraInvariants := by
  simp only [mem_invariants, mem_symmetricAlgebraInvariants, Subtype.ext_iff,
    coe_symmetricAlgebraHomogeneous_apply]

/-- The invariants of the action over the invariant subalgebra are the invariant subalgebra. -/
theorem mem_invariants_symmetricAlgebraOverInvariants_iff (p : SymmetricAlgebra R M) :
    p ∈ ρ.symmetricAlgebraOverInvariants.invariants ↔ p ∈ ρ.symmetricAlgebraInvariants := by
  simp [mem_invariants]

/-- The invariants of the degree-`n` representation are the degree-`n` part of the invariant
subalgebra. -/
theorem map_subtype_invariants_symmetricAlgebraHomogeneous (n : ℕ) :
    (ρ.symmetricAlgebraHomogeneous n).invariants.map (homogeneousSubmodule R M n).subtype =
      Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants ⊓ homogeneousSubmodule R M n := by
  ext p
  simp only [Submodule.mem_map, Submodule.coe_subtype, Submodule.mem_inf,
    Subalgebra.mem_toSubmodule]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(ρ.mem_invariants_symmetricAlgebraHomogeneous_iff q).1 hq, q.2⟩
  · rintro ⟨hp, hpn⟩
    exact ⟨⟨p, hpn⟩, (ρ.mem_invariants_symmetricAlgebraHomogeneous_iff ⟨p, hpn⟩).2 hp, rfl⟩

/-- The invariants of the degree-`n` representation have the dimension of the degree-`n` part of
the invariant subalgebra. -/
theorem finrank_invariants_symmetricAlgebraHomogeneous (n : ℕ) :
    Module.finrank R (ρ.symmetricAlgebraHomogeneous n).invariants =
      Module.finrank R
        ↥(Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants ⊓ homogeneousSubmodule R M n) := by
  rw [← map_subtype_invariants_symmetricAlgebraHomogeneous, Submodule.finrank_map_subtype_eq]

/-- **Integrality over the invariants.** For a finite group, the symmetric algebra is integral
over the invariant subalgebra: each `p` is a root of the monic orbit polynomial
`∏ g, (X - g • p)`, whose coefficients are invariant. -/
instance isIntegral_symmetricAlgebraInvariants [Finite G] :
    Algebra.IsIntegral ρ.symmetricAlgebraInvariants (SymmetricAlgebra R M) :=
  letI := ρ.symmetricAlgebraMulSemiringAction
  haveI := ρ.isInvariant_symmetricAlgebraInvariants
  Algebra.IsInvariant.isIntegral _ _ G

end CommRing

end Representation
