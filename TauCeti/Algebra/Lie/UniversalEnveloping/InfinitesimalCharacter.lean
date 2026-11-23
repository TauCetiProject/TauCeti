/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode
public import TauCeti.Algebra.Lie.UniversalEnveloping.CenterEigenspace
public import TauCeti.Algebra.Lie.UniversalEnveloping.Dual

/-!
# Generalized infinitesimal characters

Let `M` be a module over a Lie algebra `L` over a commutative ring `R`, and let
`Z = Z(U(L))` be the centre of the universal enveloping algebra. The centre acts on `M` through
the `R`-algebra homomorphism `TauCeti.UniversalEnvelopingAlgebra.centralAction`, by operators
commuting with the Lie action. For an algebra character `χ : Z →ₐ[R] R`, the module has
infinitesimal character `χ` when every `z ∈ Z` acts by the scalar `χ z`, that is when the centre
eigenspace `TauCeti.UniversalEnvelopingAlgebra.centerEigenspace R L M χ` is everything.

Extensions of such modules need not have an infinitesimal character: the two-by-two Jordan block
with eigenvalue `c` for the one-dimensional abelian Lie algebra is not scalar. What survives is
**generalized `χ`-finiteness**: every vector is annihilated by some power of the ideal `ker χ` of
`Z`. The vectors with this property form the Lie submodule
`TauCeti.UniversalEnvelopingAlgebra.generalizedCharacter R L M χ`. The power is allowed to depend
on the vector; asking for one power of `ker χ` that annihilates the whole module is a stronger,
uniform condition (`TauCeti.UniversalEnvelopingAlgebra.isGeneralizedCharacterFinite_of_pow`).
Generalized `χ`-finiteness passes to Lie submodules and quotients, and more generally along
injective and surjective homomorphisms of Lie modules.

On the dual module the centre acts through the antipode, the principal anti-automorphism
`x ↦ -x` of `U(L)`, which maps `Z` to itself and is an algebra automorphism there. So the dual
of a module with infinitesimal character `χ` has infinitesimal character
`TauCeti.UniversalEnvelopingAlgebra.dualCharacter χ = χ ∘ antipode`, and the uniform annihilation
by a power of `ker χ` dualizes in the same way. On a central element of degree one the dual
character is the negative: on the central one-dimensional Lie algebra a scalar action `2`
dualizes to `-2`.

For an abelian Lie algebra every element of `U(L)` is central, and every linear functional
`λ : L → R` is the restriction to `L` of an infinitesimal character
(`TauCeti.UniversalEnvelopingAlgebra.abelianCharacter`); for `gl₁` this says that every scalar is
the value of an infinitesimal character on the generator.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.centralAction`: the action of `Z(U(L))` on a Lie module.
* `TauCeti.UniversalEnvelopingAlgebra.generalizedCharacter`: the Lie submodule of vectors
  annihilated by some power of `ker χ`.
* `TauCeti.UniversalEnvelopingAlgebra.IsGeneralizedCharacterFinite`: every vector is annihilated
  by some power of `ker χ`.
* `TauCeti.UniversalEnvelopingAlgebra.centerAntipode`: the antipode restricted to the centre, an
  algebra automorphism.
* `TauCeti.UniversalEnvelopingAlgebra.dualCharacter`: the character `χ ∘ antipode` of the dual
  module.
* `TauCeti.UniversalEnvelopingAlgebra.abelianCharacter`: the character of `U(L)` extending a
  linear functional on an abelian Lie algebra.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.centerEigenspace_le_generalizedCharacter`: an infinitesimal
  character is a generalized one.
* `TauCeti.UniversalEnvelopingAlgebra.IsGeneralizedCharacterFinite.of_injective`,
  `TauCeti.UniversalEnvelopingAlgebra.IsGeneralizedCharacterFinite.of_surjective`, and the
  submodule and quotient instances: closure under subquotients.
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

variable (R L) in
/-- The antipode of `U(L)` maps the centre into itself. -/
theorem antipode_mem_center {z : U} (hz : z ∈ Subalgebra.center R U) :
    _root_.UniversalEnvelopingAlgebra.antipode R z ∈ Subalgebra.center R U := by
  rw [Subalgebra.mem_center_iff]
  intro a
  obtain ⟨b, rfl⟩ := (_root_.UniversalEnvelopingAlgebra.antipode_bijective (L := L) R).2 a
  rw [← _root_.UniversalEnvelopingAlgebra.antipode_mul_antidistrib,
    ← _root_.UniversalEnvelopingAlgebra.antipode_mul_antidistrib,
    Subalgebra.mem_center_iff.mp hz b]

variable (R L) in
/-- The antipode restricted to the centre of `U(L)`. On the commutative centre the
anti-automorphism `x ↦ -x` is an algebra homomorphism. -/
noncomputable def centerAntipode : Subalgebra.center R U →ₐ[R] Subalgebra.center R U where
  toFun z :=
    ⟨_root_.UniversalEnvelopingAlgebra.antipode R (z : U), antipode_mem_center R L z.property⟩
  map_one' := Subtype.ext (_root_.UniversalEnvelopingAlgebra.antipode_one R)
  map_mul' z w := Subtype.ext <| by
    change _root_.UniversalEnvelopingAlgebra.antipode R ((z : U) * (w : U)) =
      _root_.UniversalEnvelopingAlgebra.antipode R (z : U) *
        _root_.UniversalEnvelopingAlgebra.antipode R (w : U)
    rw [_root_.UniversalEnvelopingAlgebra.antipode_mul_antidistrib]
    exact Subalgebra.mem_center_iff.mp (antipode_mem_center R L z.property) _
  map_zero' := Subtype.ext (map_zero _)
  map_add' z w := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext (_root_.UniversalEnvelopingAlgebra.antipode_algebraMap R r)

@[simp]
theorem coe_centerAntipode (z : Subalgebra.center R U) :
    (centerAntipode R L z : U) = _root_.UniversalEnvelopingAlgebra.antipode R (z : U) :=
  (rfl)

/-- The antipode of the centre is an involution. -/
@[simp]
theorem centerAntipode_centerAntipode (z : Subalgebra.center R U) :
    centerAntipode R L (centerAntipode R L z) = z :=
  Subtype.ext (_root_.UniversalEnvelopingAlgebra.antipode_antipode R (z : U))

/-- The **dual character** `χ ∘ antipode` of a character of the centre of `U(L)`: the centre acts
on the dual of a module with infinitesimal character `χ` through it. -/
noncomputable def dualCharacter (χ : Subalgebra.center R U →ₐ[R] R) :
    Subalgebra.center R U →ₐ[R] R :=
  χ.comp (centerAntipode R L)

@[simp]
theorem dualCharacter_apply (χ : Subalgebra.center R U →ₐ[R] R) (z : Subalgebra.center R U) :
    dualCharacter χ z = χ (centerAntipode R L z) :=
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
  exact Subtype.ext (_root_.UniversalEnvelopingAlgebra.antipode_ι R y)

/-- The centre acts on the dual module through the antipode. -/
theorem centralAction_dual_apply (z : Subalgebra.center R U) (φ : Dual R M) (m : M) :
    centralAction R L (Dual R M) z φ m = φ (centralAction R L M (centerAntipode R L z) m) := by
  rw [centralAction_apply, _root_.UniversalEnvelopingAlgebra.representation_dual_apply,
    hopfAlgebraStructAntipode_eq_antipode]
  rfl

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
  have hle : Ideal.map (centerAntipode R L) (RingHom.ker (dualCharacter χ)) ≤ RingHom.ker χ := by
    rw [Ideal.map_le_iff_le_comap]
    intro w hw
    rwa [Ideal.mem_comap, RingHom.mem_ker, ← dualCharacter_apply, ← RingHom.mem_ker]
  have hmem : centerAntipode R L z ∈ RingHom.ker χ ^ n := by
    refine Ideal.pow_right_mono hle n ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hz
  ext φ m
  rw [centralAction_dual_apply, h _ hmem, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
    LinearMap.zero_apply]

/-! ### Abelian Lie algebras -/

section Abelian

variable [IsLieAbelian L]

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L) in
/-- A linear functional on an abelian Lie algebra, viewed as a Lie algebra homomorphism to the
abelian Lie algebra `R`. -/
private def linearToLieHom (f : L →ₗ[R] R) : L →ₗ⁅R⁆ R :=
  { f with
    map_lie' := by
      intro y y'
      change f ⁅y, y'⁆ = ⁅f y, f y'⁆
      rw [trivial_lie_zero, map_zero, Ring.lie_def, mul_comm, sub_self] }

variable (R L) in
/-- The **infinitesimal character of an abelian Lie algebra extending a linear functional**
`f : L → R`: every element of `U(L)` is central, and `U(L) → R` is the algebra homomorphism
extending `f`. For `gl₁` it shows that every scalar is the value of an infinitesimal character
on the generator. -/
noncomputable def abelianCharacter (f : L →ₗ[R] R) : Subalgebra.center R U →ₐ[R] R :=
  (_root_.UniversalEnvelopingAlgebra.lift R (linearToLieHom R L f)).comp
    (Subalgebra.center R U).val

/-- In `U(L)` for an abelian Lie algebra `L`, the canonical generators are central. -/
theorem ι_mem_center (y : L) :
    _root_.UniversalEnvelopingAlgebra.ι R y ∈ Subalgebra.center R U := by
  rw [Subalgebra.center_eq_top]
  trivial

/-- The character extending a linear functional takes the value of the functional on a
generator. -/
theorem abelianCharacter_ι (f : L →ₗ[R] R) (y : L) :
    abelianCharacter R L f ⟨_, ι_mem_center y⟩ = f y := by
  simp only [abelianCharacter, AlgHom.comp_apply, Subalgebra.coe_val,
    _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

end Abelian

end TauCeti.UniversalEnvelopingAlgebra
