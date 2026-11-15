/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Subalgebra.Character
public import TauCeti.Algebra.Lie.Current.CentralExtension
public import TauCeti.Algebra.Lie.Current.Topology
public import TauCeti.Algebra.Lie.Extension.Topology

/-!
# Canonical splittings over nonnegative-order currents

The currents of order at least `n ≥ 0` form a Lie subalgebra `a_n`. The residue cocycle
vanishes on this subalgebra, so the zero-central-coordinate section is a Lie homomorphism.
The preimage of `a_n` in the residue extension is canonically the direct product `a_n × R`.
The zero-central-coordinate sections agree under inclusion of higher-order currents and are
continuous. The product splitting is continuous when `R` is discrete, and its inverse is
continuous for any topology on `R`.

The central-coordinate character, scaled by any `a : R`, kills `a_n` and takes the value
`a` on the distinguished central generator. It specifies the one-dimensional representation
used to induce vacuum and congruence modules. All constructions include `n = 0`, arbitrary
invariant symmetric forms (including zero), and arbitrary commutative coefficient rings.

The residue convention is `Res(f dg) Φ(x,y)`, so the affine level form is `κ = -Φ`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.1 and §3.2.
-/

public section

noncomputable section

open LieAlgebra
open LieAlgebra.ofTwoCocycle (centralElement ofProd_symm_centralElement)

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local instance : IsLieAbelian R := ⟨fun x y ↦ by
  simp [LieRing.of_associative_ring_bracket, mul_comm]⟩

local notation "C" => currentAlgebra R L
local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "E" => ofTwoCocycle c

/-- The preimage `a_n ⊕ R K` of the order Lie subalgebra in the residue extension. -/
def orderExtensionLieSubalgebra (n : ℕ) : LieSubalgebra R E :=
  (orderLieSubalgebra R L n).comap (ofTwoCocycle.proj c)

/-- An element lies in the central preimage exactly when its projection has the required order. -/
@[simp]
theorem mem_orderExtensionLieSubalgebra (n : ℕ) (v : E) :
    v ∈ orderExtensionLieSubalgebra Φ hΦ hΦs n ↔
      ofTwoCocycle.proj c v ∈ orderLieSubalgebra R L n :=
  (Iff.rfl)

/-- The central preimages decrease with the order. -/
theorem orderExtensionLieSubalgebra_antitone :
    Antitone (orderExtensionLieSubalgebra Φ hΦ hΦs) :=
  fun _ _ h _ hu ↦ orderLieSubalgebra_antitone R L h hu

/-- The residue cocycle vanishes on every nonnegative-order current subalgebra. -/
theorem twoCocycleOfBilinear_eq_zero_of_mem_orderLieSubalgebra (n : ℕ)
    (x : C) (hx : x ∈ orderLieSubalgebra R L n)
    (y : C) (hy : y ∈ orderLieSubalgebra R L n) :
    (c : LieModule.Cohomology.twoCochain R C (TrivialLieModule R C R)) x y = 0 := by
  simp only [twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply]
  exact residuePairing_eq_zero_of_mem_orderSubmodule_zero R L Φ
    (orderSubmodule_antitone R L (Int.natCast_nonneg n)
      ((mem_orderLieSubalgebra R L n x).mp hx))
    (orderSubmodule_antitone R L (Int.natCast_nonneg n)
      ((mem_orderLieSubalgebra R L n y).mp hy))

/-- The canonical splitting of the central preimage as a direct product of Lie algebras. -/
def orderExtensionEquiv (n : ℕ) :
    (orderLieSubalgebra R L n × R) ≃ₗ⁅R⁆ orderExtensionLieSubalgebra Φ hΦ hΦs n :=
  ofTwoCocycle.splitEquivOfVanishing c (orderLieSubalgebra R L n)
    (TrivialLieModule.equiv R C R)
    (twoCocycleOfBilinear_eq_zero_of_mem_orderLieSubalgebra Φ hΦ hΦs n)

/-- Forward coordinates of the canonical splitting. -/
@[simp]
theorem coe_orderExtensionEquiv (n : ℕ) (p : orderLieSubalgebra R L n × R) :
    (orderExtensionEquiv Φ hΦ hΦs n p : E) =
      ofProd c (p.1, (TrivialLieModule.equiv R C R).symm p.2) :=
  ofTwoCocycle.coe_splitEquivOfVanishing c _ _ _ p

/-- Inverse coordinates of the canonical splitting. -/
@[simp]
theorem orderExtensionEquiv_symm_apply (n : ℕ)
    (v : orderExtensionLieSubalgebra Φ hΦ hΦs n) :
    (orderExtensionEquiv Φ hΦ hΦs n).symm v =
      (⟨ofTwoCocycle.proj c v,
          (mem_orderExtensionLieSubalgebra Φ hΦ hΦs n v).mp v.property⟩,
        TrivialLieModule.equiv R C R ((ofProd c).symm v).2) :=
  ofTwoCocycle.splitEquivOfVanishing_symm_apply c _ _ _ v

/-- The canonical Lie section over currents of nonnegative order, with central coordinate zero. -/
def orderSection (n : ℕ) : orderLieSubalgebra R L n →ₗ⁅R⁆ E :=
  ofTwoCocycle.sectionOfVanishing c (orderLieSubalgebra R L n)
    (twoCocycleOfBilinear_eq_zero_of_mem_orderLieSubalgebra Φ hΦ hΦs n)

/-- The section puts zero in the central coordinate. -/
@[simp]
theorem orderSection_apply (n : ℕ) (u : orderLieSubalgebra R L n) :
    orderSection Φ hΦ hΦs n u = ofProd c (u, 0) := by
  simp [orderSection]

/-- Canonical sections agree under inclusion of higher-order currents. -/
theorem orderSection_inclusion {m n : ℕ} (h : n ≤ m) (u : orderLieSubalgebra R L m) :
    orderSection Φ hΦ hΦs n
      (LieSubalgebra.inclusion (orderLieSubalgebra_antitone R L h) u) =
        orderSection Φ hΦ hΦs m u := by
  simp

/-- `a` times the central coordinate of the residue extension. -/
def centralCoordinateForm (a : R) : E →ₗ[R] R :=
  a • ((TrivialLieModule.equiv R C R).toLinearMap ∘ₗ LinearMap.snd R _ _ ∘ₗ
    (ofProdLinearEquiv c).symm.toLinearMap)

/-- The scaled central-coordinate form is `a` times the coefficient coordinate. -/
theorem centralCoordinateForm_apply (a : R) (v : E) :
    centralCoordinateForm Φ hΦ hΦs a v =
      a * TrivialLieModule.equiv R C R ((ofProd c).symm v).2 := by
  simp [centralCoordinateForm, coe_ofProdLinearEquiv_symm]

/-- The scaled central-coordinate form evaluates to `a z` in product coordinates. -/
@[simp]
theorem centralCoordinateForm_ofProd (a : R) (u : C) (z : TrivialLieModule R C R) :
    centralCoordinateForm Φ hΦ hΦs a (ofProd c (u, z)) =
      a * TrivialLieModule.equiv R C R z := by
  simp [centralCoordinateForm_apply]

/-- The central-coordinate form vanishes on brackets of nonnegative-order currents in the
extension, since their cocycle is zero. -/
theorem centralCoordinateForm_lie_eq_zero (a : R) (n : ℕ) :
    ∀ x ∈ orderExtensionLieSubalgebra Φ hΦ hΦs n,
      ∀ y ∈ orderExtensionLieSubalgebra Φ hΦ hΦs n,
      centralCoordinateForm Φ hΦ hΦs a ⁅x, y⁆ = 0 := by
  intro x hx y hy
  let χ := (LieHom.snd R (orderLieSubalgebra R L n) R).comp
    (orderExtensionEquiv Φ hΦ hΦs n).symm.toLieHom
  have h := lieCharacter_apply_lie χ ⟨x, hx⟩ ⟨y, hy⟩
  simp only [χ, LieHom.comp_apply, LieHom.snd_apply, LieEquiv.coe_toLieHom,
    orderExtensionEquiv_symm_apply, LieSubalgebra.coe_bracket] at h
  rw [centralCoordinateForm_apply, h, mul_zero]

/-- The central-coordinate character with central value `a`, killing the order currents. -/
def orderCharacter (a : R) (n : ℕ) :
    LieCharacter R (orderExtensionLieSubalgebra Φ hΦ hΦs n) :=
  (orderExtensionLieSubalgebra Φ hΦ hΦs n).restrictCharacter
    (centralCoordinateForm Φ hΦ hΦs a)
    (centralCoordinateForm_lie_eq_zero Φ hΦ hΦs a n)

/-- The inducing character is `a` times the central coordinate. -/
theorem orderCharacter_apply (a : R) (n : ℕ)
    (v : orderExtensionLieSubalgebra Φ hΦ hΦs n) :
    orderCharacter Φ hΦ hΦs a n v =
      a * TrivialLieModule.equiv R C R ((ofProd c).symm v).2 := by
  simp [orderCharacter, centralCoordinateForm_apply]

/-- The distinguished central generator belongs to every central preimage. -/
theorem centralElement_mem_orderExtensionLieSubalgebra (n : ℕ) :
    centralElement c ∈ orderExtensionLieSubalgebra Φ hΦ hΦs n := by
  rw [mem_orderExtensionLieSubalgebra, ofTwoCocycle.proj_apply,
    ofProd_symm_centralElement]
  exact zero_mem _

/-- The global central-coordinate form takes the value `a` on the central generator. -/
@[simp]
theorem centralCoordinateForm_centralElement (a : R) :
    centralCoordinateForm Φ hΦ hΦs a (centralElement c) = a := by
  simp [centralCoordinateForm_apply, ofProd_symm_centralElement]

/-- The inducing character takes the prescribed value on the central generator. -/
@[simp]
theorem orderCharacter_centralElement (a : R) (n : ℕ) :
    orderCharacter Φ hΦ hΦs a n
      ⟨centralElement c, centralElement_mem_orderExtensionLieSubalgebra Φ hΦ hΦs n⟩ =
        a := by
  simp [orderCharacter]

/-- In split coordinates, the inducing character is `a` times the scalar coordinate. -/
@[simp]
theorem orderCharacter_orderExtensionEquiv (a : R) (n : ℕ)
    (p : orderLieSubalgebra R L n × R) :
    orderCharacter Φ hΦ hΦs a n (orderExtensionEquiv Φ hΦ hΦs n p) = a * p.2 := by
  rw [orderCharacter_apply]
  simp

/-- The canonical Lie section is continuous for the induced order topology. -/
theorem continuous_orderSection (n : ℕ) : Continuous (orderSection Φ hΦ hΦs n) :=
  ofTwoCocycle.continuous_sectionOfVanishing c _ _

/-- With discrete scalars, the splitting is continuous for the product and subspace topologies. -/
theorem continuous_orderExtensionEquiv [TopologicalSpace R] [DiscreteTopology R] (n : ℕ) :
    Continuous (orderExtensionEquiv Φ hΦ hΦs n) :=
  ofTwoCocycle.continuous_splitEquivOfVanishing c _ _ _

/-- The inverse splitting is continuous for any topology on the scalar target: its central
coordinate is locally constant. -/
theorem continuous_orderExtensionEquiv_symm [TopologicalSpace R] (n : ℕ) :
    Continuous (orderExtensionEquiv Φ hΦ hΦs n).symm :=
  ofTwoCocycle.continuous_splitEquivOfVanishing_symm c _ _ _

end TauCeti.CurrentAlgebra
