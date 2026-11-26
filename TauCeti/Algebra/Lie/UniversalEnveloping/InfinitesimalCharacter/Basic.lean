/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Character
public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode
public import TauCeti.Algebra.Lie.UniversalEnveloping.CenterEigenspace
public import TauCeti.Algebra.Lie.UniversalEnveloping.Dual

/-!
# Infinitesimal characters and generalized infinitesimal characters

Let `M` be a module over a Lie algebra `L` over a commutative ring `R`, and let
`Z = Z(U(L))` be the centre of the universal enveloping algebra. The centre acts on `M` through
the `R`-algebra homomorphism `TauCeti.UniversalEnvelopingAlgebra.centralAction`, by operators
commuting with the Lie action. For an algebra character `χ : Z →ₐ[R] R`, the module **has
infinitesimal character `χ`** (`TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter`)
when every `z ∈ Z` acts by the scalar `χ z`, that is when the centre eigenspace
`TauCeti.UniversalEnvelopingAlgebra.centerEigenspace R L M χ` is everything. This predicate is
preserved by homomorphisms of Lie modules: it passes to Lie submodules and quotients, and more
generally along injective and surjective homomorphisms. The zero module has every infinitesimal
character, so uniqueness of the infinitesimal character needs a nonzero module
(`HasInfinitesimalCharacter.eq`, for a module without `R`-torsion).

Extensions of such modules need not have an infinitesimal character: the two-by-two Jordan block
with eigenvalue `c` for the one-dimensional abelian Lie algebra is not scalar. What survives is
**generalized `χ`-finiteness**: every vector is annihilated by some power of the ideal `ker χ` of
`Z`. The vectors with this property form the Lie submodule
`TauCeti.UniversalEnvelopingAlgebra.generalizedCharacter R L M χ`. The power is allowed to depend
on the vector; asking for one power of `ker χ` that annihilates the whole module is a stronger,
uniform condition (`TauCeti.UniversalEnvelopingAlgebra.isGeneralizedCharacterFinite_of_pow`).
Generalized `χ`-finiteness passes to Lie submodules and quotients, and more generally along
injective and surjective homomorphisms of Lie modules.

On the dual module the centre acts through the antipode, the principal anti-automorphism of
`U(L)` extending `x ↦ -x` on `L`, which maps `Z` to itself and is an algebra automorphism there
(`UniversalEnvelopingAlgebra.centerAntipode`). So the dual of a module with infinitesimal
character `χ` has infinitesimal character
`TauCeti.UniversalEnvelopingAlgebra.dualCharacter χ = χ ∘ antipode`, and the uniform annihilation
by a power of `ker χ` dualizes in the same way. On a central element of degree one the dual
character is the negative: on the central one-dimensional Lie algebra a scalar action `2`
dualizes to `-2`.

Every Lie algebra homomorphism `f : L → R` extends to `U(L)`, and restricting to the centre gives
the character `TauCeti.UniversalEnvelopingAlgebra.liftCharacter f`, which takes the value `f y` on
a central generator `ι y`. For an abelian Lie algebra every element of `U(L)` is central and every
linear functional is a Lie algebra homomorphism, so every linear functional is the restriction to
`L` of an infinitesimal character; for `gl₁` this says that every scalar is the value of an
infinitesimal character on the generator.

If `L` acts on `M` through a Lie algebra homomorphism `f : L → R`, that is `⁅y, m⁆ = f y • m`,
then every `u ∈ U(L)` acts by the scalar `lift f u`
(`TauCeti.UniversalEnvelopingAlgebra.representation_apply_of_lie_eq_smul`, in
`TauCeti/Algebra/Lie/UniversalEnveloping/Basic.lean`), so `M` has the infinitesimal
character `liftCharacter R L f` extending `f`
(`HasInfinitesimalCharacter.of_lie_eq_smul`); the trivial module is the case `f = 0`. The values
of these characters on the trace-form Casimir of `gl n` are computed in
`TauCeti/Algebra/Lie/GeneralLinear/InfinitesimalCharacter.lean`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.centralAction`: the action of `Z(U(L))` on a Lie module.
* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter`: every central element acts by
  the scalar `χ z`.
* `TauCeti.UniversalEnvelopingAlgebra.generalizedCharacter`: the Lie submodule of vectors
  annihilated by some power of `ker χ`.
* `TauCeti.UniversalEnvelopingAlgebra.IsGeneralizedCharacterFinite`: every vector is annihilated
  by some power of `ker χ`.
* `TauCeti.UniversalEnvelopingAlgebra.dualCharacter`: the character `χ ∘ antipode` of the dual
  module.
* `TauCeti.UniversalEnvelopingAlgebra.liftCharacter`: the character of the centre of `U(L)`
  extending a Lie algebra homomorphism `L → R`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.hasInfinitesimalCharacter_iff`,
  `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.apply`: the defining property.
* `TauCeti.UniversalEnvelopingAlgebra.hasInfinitesimalCharacter_iff_centerEigenspace_eq_top`.
* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.of_injective`, `.of_surjective`,
  `.lieSubmodule`, `.quotient`: invariance under homomorphisms of Lie modules.
* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.eq`: uniqueness for a nonzero
  torsion-free module.
* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.dual`: the dual of a module with
  infinitesimal character `χ` has infinitesimal character `dualCharacter χ`.
* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.of_lie_eq_smul`,
  `TauCeti.UniversalEnvelopingAlgebra.hasInfinitesimalCharacter_of_isTrivial`: modules on which
  `L` acts through a character.
* `TauCeti.UniversalEnvelopingAlgebra.centerEigenspace_le_generalizedCharacter`: an infinitesimal
  character is a generalized one.
* `TauCeti.UniversalEnvelopingAlgebra.IsGeneralizedCharacterFinite.of_injective`,
  `TauCeti.UniversalEnvelopingAlgebra.IsGeneralizedCharacterFinite.of_surjective`,
  `TauCeti.UniversalEnvelopingAlgebra.IsGeneralizedCharacterFinite.lieSubmodule`, `.quotient` and
  `.subquotient`: closure under subquotients.
* `TauCeti.UniversalEnvelopingAlgebra.centerEigenspace_dual_eq_top`: the dual of a module with
  infinitesimal character `χ` has infinitesimal character `dualCharacter χ`.
* `TauCeti.UniversalEnvelopingAlgebra.centralAction_dual_eq_zero_of_mem_pow`: uniform
  annihilation by a power of `ker χ` dualizes.
* `TauCeti.UniversalEnvelopingAlgebra.dualCharacter_ι`: on a central element of degree one the
  dual character is the negative.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. **199** (2014), §4.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Module

universe u v w x

variable (R : Type u) (L : Type v) (M : Type w) (N : Type x)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-! ### The action of the centre -/

/-- The action of the centre `Z(U(L))` of the enveloping algebra on a Lie module, as an algebra
homomorphism to the endomorphisms of the module. -/
noncomputable def centralAction : Subalgebra.center R U →ₐ[R] End R M :=
  (representation R L M).comp (Subalgebra.center R U).val

variable {R L M N}

@[simp]
theorem centralAction_apply (z : Subalgebra.center R U) (m : M) :
    centralAction R L M z m = representation R L M (z : U) m :=
  (rfl)

/-- A central element acts by an endomorphism of the Lie module. -/
theorem centralAction_lie (z : Subalgebra.center R U) (y : L) (m : M) :
    centralAction R L M z ⁅y, m⁆ = ⁅y, centralAction R L M z m⁆ :=
  representation_lie_of_mem_center R L M z.property y m

/-- A homomorphism of Lie modules intertwines the actions of the centre. -/
theorem map_centralAction (f : M →ₗ⁅R,L⁆ N) (z : Subalgebra.center R U) (m : M) :
    f (centralAction R L M z m) = centralAction R L N z (f m) :=
  map_representation R L M N f (z : U) m

/-! ### Generalized characters -/

variable (R L M) in
/-- The **generalized `χ`-eigenspace** of the centre: the Lie submodule of vectors annihilated by
some power of the ideal `ker χ` of `Z(U(L))`. The power may depend on the vector. -/
noncomputable def generalizedCharacter (χ : Subalgebra.center R U →ₐ[R] R) :
    LieSubmodule R L M where
  carrier := {m | ∃ n : ℕ, ∀ z ∈ RingHom.ker χ ^ n, centralAction R L M z m = 0}
  add_mem' := by
    rintro m₁ m₂ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
    refine ⟨max n₁ n₂, fun z hz => ?_⟩
    rw [map_add, h₁ z (Ideal.pow_le_pow_right (le_max_left _ _) hz),
      h₂ z (Ideal.pow_le_pow_right (le_max_right _ _) hz), add_zero]
  zero_mem' := ⟨0, fun z _ => map_zero _⟩
  smul_mem' := by
    rintro r m ⟨n, h⟩
    exact ⟨n, fun z hz => by rw [map_smul, h z hz, smul_zero]⟩
  lie_mem := by
    rintro y m ⟨n, h⟩
    exact ⟨n, fun z hz => by rw [centralAction_lie, h z hz, lie_zero]⟩

/-- A vector lies in the generalized `χ`-eigenspace exactly when some power of `ker χ`
annihilates it. -/
@[simp]
theorem mem_generalizedCharacter {χ : Subalgebra.center R U →ₐ[R] R} {m : M} :
    m ∈ generalizedCharacter R L M χ ↔
      ∃ n : ℕ, ∀ z ∈ RingHom.ker χ ^ n, centralAction R L M z m = 0 :=
  Iff.rfl

/-- **An infinitesimal character is a generalized character**: an eigenvector of the centre for
`χ` is annihilated by `ker χ` itself. -/
theorem centerEigenspace_le_generalizedCharacter (χ : Subalgebra.center R U →ₐ[R] R) :
    centerEigenspace R L M χ ≤ generalizedCharacter R L M χ := by
  intro m hm
  refine ⟨1, fun z hz => ?_⟩
  rw [pow_one, RingHom.mem_ker] at hz
  rw [centralAction_apply, mem_centerEigenspace.mp hm z, hz, zero_smul]

/-- A homomorphism of Lie modules carries the generalized `χ`-eigenspace into the generalized
`χ`-eigenspace. -/
theorem _root_.LieModuleHom.map_generalizedCharacter_le (f : M →ₗ⁅R,L⁆ N)
    (χ : Subalgebra.center R U →ₐ[R] R) :
    (generalizedCharacter R L M χ).map f ≤ generalizedCharacter R L N χ := by
  rw [LieSubmodule.map_le_iff_le_comap]
  rintro m ⟨n, h⟩
  refine ⟨n, fun z hz => ?_⟩
  rw [LieModuleHom.coe_toLinearMap, ← map_centralAction, h z hz, map_zero]

variable (R L M) in
/-- **Generalized `χ`-finiteness**: every vector of the Lie module is annihilated by some power
of the ideal `ker χ` of `Z(U(L))`. The power may depend on the vector, as for a direct sum of
Jordan blocks of unbounded size. -/
def IsGeneralizedCharacterFinite (χ : Subalgebra.center R U →ₐ[R] R) : Prop :=
  ∀ m : M, ∃ n : ℕ, ∀ z ∈ RingHom.ker χ ^ n, centralAction R L M z m = 0

/-- A module is generalized `χ`-finite exactly when its generalized `χ`-eigenspace is
everything. -/
theorem isGeneralizedCharacterFinite_iff_generalizedCharacter_eq_top
    {χ : Subalgebra.center R U →ₐ[R] R} :
    IsGeneralizedCharacterFinite R L M χ ↔ generalizedCharacter R L M χ = ⊤ := by
  rw [eq_top_iff]
  exact ⟨fun h m _ => h m, fun h m => h (LieSubmodule.mem_top m)⟩

/-- A module with infinitesimal character `χ` is generalized `χ`-finite. -/
theorem isGeneralizedCharacterFinite_of_centerEigenspace_eq_top
    {χ : Subalgebra.center R U →ₐ[R] R} (h : centerEigenspace R L M χ = ⊤) :
    IsGeneralizedCharacterFinite R L M χ := by
  rw [isGeneralizedCharacterFinite_iff_generalizedCharacter_eq_top, eq_top_iff, ← h]
  exact centerEigenspace_le_generalizedCharacter χ

/-- **Uniform annihilation implies generalized `χ`-finiteness**: if one power of `ker χ`
annihilates the whole module, every vector is annihilated by a power of `ker χ`. -/
theorem isGeneralizedCharacterFinite_of_pow {χ : Subalgebra.center R U →ₐ[R] R} (n : ℕ)
    (h : ∀ z ∈ RingHom.ker χ ^ n, centralAction R L M z = 0) :
    IsGeneralizedCharacterFinite R L M χ :=
  fun m => ⟨n, fun z hz => by rw [h z hz, LinearMap.zero_apply]⟩

namespace IsGeneralizedCharacterFinite

/-- Generalized `χ`-finiteness passes along an injective homomorphism of Lie modules, in
particular to Lie submodules. -/
theorem of_injective {χ : Subalgebra.center R U →ₐ[R] R}
    (h : IsGeneralizedCharacterFinite R L M χ) (f : N →ₗ⁅R,L⁆ M)
    (hf : Function.Injective f) : IsGeneralizedCharacterFinite R L N χ := by
  intro m
  obtain ⟨n, hn⟩ := h (f m)
  exact ⟨n, fun z hz => hf <| by rw [map_centralAction, hn z hz, map_zero]⟩

/-- Generalized `χ`-finiteness passes along a surjective homomorphism of Lie modules, in
particular to quotients. -/
theorem of_surjective {χ : Subalgebra.center R U →ₐ[R] R}
    (h : IsGeneralizedCharacterFinite R L M χ) (f : M →ₗ⁅R,L⁆ N)
    (hf : Function.Surjective f) : IsGeneralizedCharacterFinite R L N χ := by
  intro m
  obtain ⟨m, rfl⟩ := hf m
  obtain ⟨n, hn⟩ := h m
  exact ⟨n, fun z hz => by rw [← map_centralAction, hn z hz, map_zero]⟩

/-- A Lie submodule of a generalized `χ`-finite module is generalized `χ`-finite. -/
theorem lieSubmodule {χ : Subalgebra.center R U →ₐ[R] R}
    (h : IsGeneralizedCharacterFinite R L M χ) (P : LieSubmodule R L M) :
    IsGeneralizedCharacterFinite R L P χ :=
  h.of_injective P.incl Subtype.val_injective

/-- A quotient of a generalized `χ`-finite module by a Lie submodule is generalized
`χ`-finite. -/
theorem quotient {χ : Subalgebra.center R U →ₐ[R] R}
    (h : IsGeneralizedCharacterFinite R L M χ) (P : LieSubmodule R L M) :
    IsGeneralizedCharacterFinite R L (M ⧸ P) χ :=
  h.of_surjective (LieSubmodule.Quotient.mk' P) (LieSubmodule.Quotient.surjective_mk' P)

/-- A subquotient `P / Q` of a generalized `χ`-finite module, for Lie submodules `Q ≤ P`,
presented as a quotient of `P`, is generalized `χ`-finite. -/
theorem subquotient {χ : Subalgebra.center R U →ₐ[R] R}
    (h : IsGeneralizedCharacterFinite R L M χ) (P : LieSubmodule R L M)
    (Q : LieSubmodule R L P) : IsGeneralizedCharacterFinite R L (P ⧸ Q) χ :=
  (h.lieSubmodule P).quotient Q

end IsGeneralizedCharacterFinite

/-! ### The dual character -/

/-- The **dual character** `χ ∘ antipode` of a character of the centre of `U(L)`: the centre acts
on the dual of a module with infinitesimal character `χ` through it. -/
noncomputable def dualCharacter (χ : Subalgebra.center R U →ₐ[R] R) :
    Subalgebra.center R U →ₐ[R] R :=
  χ.comp (_root_.UniversalEnvelopingAlgebra.centerAntipode R).toAlgHom

@[simp]
theorem dualCharacter_apply (χ : Subalgebra.center R U →ₐ[R] R) (z : Subalgebra.center R U) :
    dualCharacter χ z = χ (_root_.UniversalEnvelopingAlgebra.centerAntipode R z) :=
  (rfl)

/-- Taking the dual character twice gives back the character. -/
@[simp]
theorem dualCharacter_dualCharacter (χ : Subalgebra.center R U →ₐ[R] R) :
    dualCharacter (dualCharacter χ) = χ :=
  AlgHom.ext fun z => by simp

/-- **The dual character negates central elements of degree one.** On the central
one-dimensional Lie algebra a scalar action `2` dualizes to `-2`. -/
theorem dualCharacter_ι (χ : Subalgebra.center R U →ₐ[R] R) {y : L}
    (hy : _root_.UniversalEnvelopingAlgebra.ι R y ∈ Subalgebra.center R U) :
    dualCharacter χ ⟨_, hy⟩ = -χ ⟨_, hy⟩ := by
  rw [dualCharacter_apply, ← map_neg]
  congr 1
  exact Subtype.ext ((_root_.UniversalEnvelopingAlgebra.coe_centerAntipode R _).trans
    (_root_.UniversalEnvelopingAlgebra.antipode_ι R y))

/-- The centre acts on the dual module through the antipode. -/
theorem centralAction_dual_apply (z : Subalgebra.center R U) (φ : Dual R M) (m : M) :
    centralAction R L (Dual R M) z φ m =
      φ (centralAction R L M (_root_.UniversalEnvelopingAlgebra.centerAntipode R z) m) := by
  rw [centralAction_apply, _root_.UniversalEnvelopingAlgebra.representation_dual_apply,
    hopfAlgebraStructAntipode_eq_antipode, centralAction_apply,
    _root_.UniversalEnvelopingAlgebra.coe_centerAntipode]

/-- **The dual of a module with infinitesimal character `χ` has infinitesimal character
`dualCharacter χ`.** -/
theorem centerEigenspace_dual_eq_top {χ : Subalgebra.center R U →ₐ[R] R}
    (h : centerEigenspace R L M χ = ⊤) :
    centerEigenspace R L (Dual R M) (dualCharacter χ) = ⊤ := by
  rw [centerEigenspace_eq_top_iff] at h ⊢
  intro z φ
  ext m
  rw [← centralAction_apply, centralAction_dual_apply, centralAction_apply, h, map_smul,
    dualCharacter_apply, LinearMap.smul_apply]

/-- **Uniform annihilation by a power of `ker χ` dualizes**: if `(ker χ)ⁿ` annihilates `M`, then
`(ker (dualCharacter χ))ⁿ` annihilates the dual module. Generalized `χ`-finiteness with a power
depending on the vector does not dualize in this way, since a functional sees every vector. -/
theorem centralAction_dual_eq_zero_of_mem_pow {χ : Subalgebra.center R U →ₐ[R] R} {n : ℕ}
    (h : ∀ z ∈ RingHom.ker χ ^ n, centralAction R L M z = 0) {z : Subalgebra.center R U}
    (hz : z ∈ RingHom.ker (dualCharacter χ) ^ n) :
    centralAction R L (Dual R M) z = 0 := by
  have hle : Ideal.map (_root_.UniversalEnvelopingAlgebra.centerAntipode R)
      (RingHom.ker (dualCharacter χ)) ≤ RingHom.ker χ := by
    rw [Ideal.map_le_iff_le_comap]
    intro w hw
    rwa [Ideal.mem_comap, RingHom.mem_ker, ← dualCharacter_apply, ← RingHom.mem_ker]
  have hmem : _root_.UniversalEnvelopingAlgebra.centerAntipode R z ∈ RingHom.ker χ ^ n := by
    refine Ideal.pow_right_mono hle n ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hz
  ext φ m
  rw [centralAction_dual_apply, h _ hmem, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
    LinearMap.zero_apply]

/-! ### Characters from Lie algebra homomorphisms -/

section LiftCharacter

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L) in
/-- The **infinitesimal character extending a Lie algebra homomorphism** `f : L → R`: the algebra
homomorphism `U(L) → R` extending `f`, restricted to the centre. -/
noncomputable def liftCharacter (f : LieAlgebra.LieCharacter R L) :
    Subalgebra.center R U →ₐ[R] R :=
  (_root_.UniversalEnvelopingAlgebra.lift R f).comp (Subalgebra.center R U).val

/-- The character extending a Lie algebra homomorphism `f` is the lift of `f` to `U(L)`, evaluated
on the centre. -/
@[simp]
theorem liftCharacter_apply (f : LieAlgebra.LieCharacter R L) (z : Subalgebra.center R U) :
    liftCharacter R L f z = _root_.UniversalEnvelopingAlgebra.lift R f (z : U) :=
  (rfl)

/-- The character extending a Lie algebra homomorphism `f` takes the value `f y` on a central
generator `ι y`. -/
theorem liftCharacter_ι (f : LieAlgebra.LieCharacter R L) {y : L}
    (hy : _root_.UniversalEnvelopingAlgebra.ι R y ∈ Subalgebra.center R U) :
    liftCharacter R L f ⟨_, hy⟩ = f y := by
  rw [liftCharacter, AlgHom.comp_apply, Subalgebra.coe_val,
    _root_.UniversalEnvelopingAlgebra.lift_ι_apply]

/-- The Lie character of an abelian Lie algebra built from a linear functional `ψ` takes the
values of `ψ`. -/
theorem _root_.LieAlgebra.lieCharacterEquivLinearDual_symm_apply_apply [IsLieAbelian L]
    (ψ : Dual R L) (x : L) : LieAlgebra.lieCharacterEquivLinearDual.symm ψ x = ψ x :=
  (rfl)

/-- **Every linear functional on an abelian Lie algebra is the restriction of an infinitesimal
character**: the character extending `f`, read as a Lie algebra homomorphism, takes the value
`f y` on every generator. For `gl₁` it shows that every scalar is the value of an infinitesimal
character on the generator. -/
theorem liftCharacter_lieCharacterEquivLinearDual_symm_ι [IsLieAbelian L] (f : Dual R L)
    (y : L) :
    liftCharacter R L (LieAlgebra.lieCharacterEquivLinearDual.symm f)
        ⟨_, ι_mem_center R L y⟩ = f y := by
  rw [liftCharacter_ι, LieAlgebra.lieCharacterEquivLinearDual_symm_apply_apply]

end LiftCharacter

/-! ### Modules with an infinitesimal character -/

variable (R L M) in
/-- A Lie module **has infinitesimal character** `χ` when every element `z` of the centre of the
universal enveloping algebra acts by the scalar `χ z`. -/
def HasInfinitesimalCharacter (χ : Subalgebra.center R U →ₐ[R] R) : Prop :=
  ∀ (z : Subalgebra.center R U) (m : M), centralAction R L M z m = χ z • m

/-- The defining property of a module with infinitesimal character `χ`. -/
theorem hasInfinitesimalCharacter_iff {χ : Subalgebra.center R U →ₐ[R] R} :
    HasInfinitesimalCharacter R L M χ ↔
      ∀ (z : Subalgebra.center R U) (m : M), centralAction R L M z m = χ z • m :=
  Iff.rfl

/-- A central element acts on a module with infinitesimal character `χ` by the scalar `χ z`. -/
theorem HasInfinitesimalCharacter.apply {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) (z : Subalgebra.center R U) (m : M) :
    centralAction R L M z m = χ z • m :=
  hasInfinitesimalCharacter_iff.mp h z m

/-- A module has infinitesimal character `χ` if and only if its centre eigenspace for `χ` is the
whole module. -/
theorem hasInfinitesimalCharacter_iff_centerEigenspace_eq_top
    {χ : Subalgebra.center R U →ₐ[R] R} :
    HasInfinitesimalCharacter R L M χ ↔ centerEigenspace R L M χ = ⊤ := by
  rw [centerEigenspace_eq_top_iff, hasInfinitesimalCharacter_iff]
  simp only [centralAction_apply]

/-- The zero module has every infinitesimal character. -/
theorem hasInfinitesimalCharacter_of_subsingleton [Subsingleton M]
    (χ : Subalgebra.center R U →ₐ[R] R) : HasInfinitesimalCharacter R L M χ :=
  hasInfinitesimalCharacter_iff.mpr fun _ _ ↦ Subsingleton.elim _ _

namespace HasInfinitesimalCharacter

/-- **Uniqueness of the infinitesimal character** of a nonzero torsion-free module. -/
theorem eq {χ : Subalgebra.center R U →ₐ[R] R}
    [IsDomain R] [Module.IsTorsionFree R M] [Nontrivial M] {χ' : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) (h' : HasInfinitesimalCharacter R L M χ') :
    χ = χ' := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  ext z
  have := (h.apply z m).symm.trans (h'.apply z m)
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at this
  exact this.resolve_right hm

/-- An infinitesimal character is a generalized one. -/
theorem isGeneralizedCharacterFinite {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) :
    IsGeneralizedCharacterFinite R L M χ :=
  isGeneralizedCharacterFinite_of_centerEigenspace_eq_top
    (hasInfinitesimalCharacter_iff_centerEigenspace_eq_top.mp h)

/-- The infinitesimal character passes along injective homomorphisms of Lie modules. -/
theorem of_injective {χ : Subalgebra.center R U →ₐ[R] R}
    (f : M →ₗ⁅R,L⁆ N) (hf : Function.Injective f)
    (h : HasInfinitesimalCharacter R L N χ) : HasInfinitesimalCharacter R L M χ :=
  hasInfinitesimalCharacter_iff.mpr fun z m ↦ hf (by rw [map_centralAction, h.apply, map_smul])

/-- The infinitesimal character passes along surjective homomorphisms of Lie modules. -/
theorem of_surjective {χ : Subalgebra.center R U →ₐ[R] R}
    (f : M →ₗ⁅R,L⁆ N) (hf : Function.Surjective f)
    (h : HasInfinitesimalCharacter R L M χ) : HasInfinitesimalCharacter R L N χ :=
  hasInfinitesimalCharacter_iff.mpr fun z n ↦ by
    obtain ⟨m, rfl⟩ := hf n
    rw [← map_centralAction, h.apply, map_smul]

/-- A Lie submodule has the infinitesimal character of the module. -/
theorem lieSubmodule {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) (N' : LieSubmodule R L M) :
    HasInfinitesimalCharacter R L N' χ :=
  h.of_injective N'.incl Subtype.val_injective

/-- A quotient has the infinitesimal character of the module. -/
theorem quotient {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) (N' : LieSubmodule R L M) :
    HasInfinitesimalCharacter R L (M ⧸ N') χ :=
  h.of_surjective (LieSubmodule.Quotient.mk' N') (LieSubmodule.Quotient.surjective_mk' N')

/-- The dual of a module with infinitesimal character `χ` has infinitesimal character
`dualCharacter χ`. -/
theorem dual {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) :
    HasInfinitesimalCharacter R L (Dual R M) (dualCharacter χ) :=
  hasInfinitesimalCharacter_iff_centerEigenspace_eq_top.mpr
    (centerEigenspace_dual_eq_top (hasInfinitesimalCharacter_iff_centerEigenspace_eq_top.mp h))

/-- **A module on which `L` acts through a character `f` has infinitesimal character
`liftCharacter R L f`.** A central element `z` acts by the scalar `liftCharacter R L f z`. -/
theorem of_lie_eq_smul (f : LieAlgebra.LieCharacter R L)
    (hf : ∀ (y : L) (m : M), ⁅y, m⁆ = f y • m) :
    HasInfinitesimalCharacter R L M (liftCharacter R L f) :=
  hasInfinitesimalCharacter_iff.mpr fun z m ↦ by
    rw [centralAction_apply, liftCharacter_apply, representation_apply_of_lie_eq_smul f hf]

end HasInfinitesimalCharacter

/-- **The trivial module has infinitesimal character `liftCharacter R L 0`.** -/
theorem hasInfinitesimalCharacter_of_isTrivial [LieModule.IsTrivial L M] :
    HasInfinitesimalCharacter R L M (liftCharacter R L 0) :=
  HasInfinitesimalCharacter.of_lie_eq_smul 0 fun y m ↦ by simp [trivial_lie_zero]

end TauCeti.UniversalEnvelopingAlgebra
