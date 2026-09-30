/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Pi
public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Transporting and decomposing the center of an algebra

Constructions on `Subalgebra.center` that Mathlib states only for `Subring.center`, or only
as an equality of subalgebras, and that are needed whenever a structure theorem presents an algebra
up to an algebra equivalence, together with the criterion for a commutative algebra to be central
and the ring of scalars a central subalgebra provides.

* `TauCeti.centerCongr` transports the center along an algebra equivalence. It is the
  `Subalgebra` counterpart of Mathlib's `Subring.centerCongr`, which sees only the ring
  structure and therefore cannot record `R`-linearity.
* `TauCeti.centerPiAlgEquiv` splits the center of a product of algebras as the product of the
  centers, upgrading Mathlib's `Subalgebra.center_pi` from an equality of subalgebras of
  `Π i, S i` to an algebra equivalence with `Π i, Subalgebra.center R (S i)`.
* `TauCeti.centerAlgEquivOfIsCentral` identifies the center of a central algebra with the base
  field, so that its dimension is one (`TauCeti.finrank_center_of_isCentral`).
* `TauCeti.isCentral_iff_surjective_algebraMap` records that a commutative algebra is central
  exactly when its structure map is surjective, the precise sense in which centrality is a strong
  condition on a field extension.
* `Subalgebra.centralSubalgebraAlgebra` makes a subalgebra of the center into a ring of scalars
  for the ambient algebra, so that finiteness and integrality over it can be stated. Its structure
  map and action are `Subalgebra.centralSubalgebraAlgebra_algebraMap_apply` and
  `Subalgebra.centralSubalgebraAlgebra_smul_def`, and
  `Subalgebra.isScalarTower_centralSubalgebraAlgebra` records that the base ring, the subalgebra
  and the ambient algebra form a scalar tower.
* `Subalgebra.centerAlgebra` gives the whole center its canonical scalar action by inclusion.
  `Subalgebra.finite_over_center_of_finite` transfers module finiteness from a central
  subalgebra to the center. `Subalgebra.finite_center_of_isNoetherian` makes the center finite
  over that subalgebra when the ambient algebra is Noetherian as a module; together with
  `Subalgebra.isNoetherianRing_center_of_finite`, this supplies a Noetherian center for
  applications of the generalized Krull intersection theorem.
-/

public section

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- The center of an algebra acts on the algebra by its inclusion. -/
instance centerAlgebra : Algebra (center R A) A :=
  (center R A).val.toRingHom.toAlgebra' fun z a =>
    (mem_center_iff.mp z.property a).symm

/-- The structure map from the center to an algebra is inclusion. -/
@[simp]
theorem centerAlgebra_algebraMap_apply (z : center R A) :
    algebraMap (center R A) A z = z := rfl

/-- The structure map from the center is the inclusion homomorphism. -/
theorem centerAlgebra_algebraMap :
    algebraMap (center R A) A = (center R A).val.toRingHom := by
  ext z
  rfl

variable (S : Subalgebra R (Subalgebra.center R A))

/-- A subalgebra of the center of an algebra acts on the ambient algebra by multiplication. -/
abbrev centralSubalgebraAlgebra : Algebra S A :=
  (((center R A).val.comp S.val).toRingHom.toAlgebra' fun s a ↦
    (mem_center_iff.mp s.1.property a).symm)

/-- The structure map of `Subalgebra.centralSubalgebraAlgebra` is the inclusion of `S` into the
ambient algebra. -/
@[simp]
theorem centralSubalgebraAlgebra_algebraMap_apply (s : S) :
    letI := centralSubalgebraAlgebra S
    algebraMap S A s = ((s : center R A) : A) :=
  rfl

/-- `Subalgebra.centralSubalgebraAlgebra` makes `S` act by multiplication in the ambient
algebra. -/
@[simp]
theorem centralSubalgebraAlgebra_smul_def (s : S) (a : A) :
    letI := centralSubalgebraAlgebra S
    s • a = ((s : center R A) : A) * a :=
  rfl

/-- `R`, a subalgebra `S` of the center, and the ambient algebra form a scalar tower: the two
actions of `R` on the ambient algebra agree because `S` acts by multiplication. -/
theorem isScalarTower_centralSubalgebraAlgebra :
    letI := centralSubalgebraAlgebra S
    IsScalarTower R S A := by
  refine ⟨fun r s a ↦ ?_⟩
  rw [centralSubalgebraAlgebra_smul_def, centralSubalgebraAlgebra_smul_def, ← smul_mul_assoc]
  congr 1

section FiniteOverCenter

/-- The local algebra structure on the ambient algebra for the finiteness transfer. -/
local instance finiteOverCenterAlgebra : Algebra S A := centralSubalgebraAlgebra S
/-- The local algebra structure on the center for the finiteness transfer. -/
local instance finiteOverCenterCenterAlgebra : Algebra S (center R A) :=
  S.val.toRingHom.toAlgebra

/-- Finiteness over a central subalgebra implies finiteness over the whole center. -/
theorem finite_over_center_of_finite [Module.Finite S A] :
    Module.Finite (center R A) A :=
  Module.Finite.of_restrictScalars_finite S (center R A) A

end FiniteOverCenter

end Subalgebra

namespace Subalgebra

section FiniteOverCentralSubalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (S : Subalgebra R (center R A))

/-- The local algebra structure on the ambient algebra for the Noetherian transfer. -/
local instance finiteOverCentralSubalgebraAlgebra : Algebra S A := centralSubalgebraAlgebra S
/-- The local algebra structure on the center for the Noetherian transfer. -/
local instance finiteOverCentralSubalgebraCenterAlgebra : Algebra S (center R A) :=
  S.val.toRingHom.toAlgebra

/-- The center, regarded as a submodule over a central subalgebra. -/
private def centerSubmodule : Submodule S A where
  carrier := (center R A : Set A)
  zero_mem' := (center R A).zero_mem
  add_mem' := fun ha hb => (center R A).add_mem ha hb
  smul_mem' := by
    intro s a ha
    exact (center R A).mul_mem s.val.property ha

/-- The action on the submodule is multiplication in the ambient algebra. -/
private theorem centerSubmodule_smul_coe (s : S) (x : centerSubmodule S) :
    ((s • x : centerSubmodule S) : A) = ((s : center R A) : A) * (x : A) := by
  rw [Submodule.coe_smul, centralSubalgebraAlgebra_smul_def]

/-- The action on the center is multiplication by the included scalar. -/
private theorem center_smul_coe (s : S) (x : center R A) :
    ((s • x : center R A) : A) = ((s : center R A) : A) * (x : A) := by
  have hmap : algebraMap S (center R A) s = (s : center R A) := rfl
  have hsmul : s • x = algebraMap S (center R A) s * x := Algebra.smul_def s x
  rw [hsmul, hmap, (center R A).coe_mul]

/-- The submodule of central elements has the canonical center's `S`-module structure. -/
private def centerSubmoduleEquiv : (centerSubmodule S) ≃ₗ[S] center R A where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s x := by
    apply Subtype.ext
    rw [center_smul_coe, centerSubmodule_smul_coe]
    simp only [RingHom.id_apply]

/-- If an algebra is Noetherian as a module over a central subalgebra, its center is
finite over that subalgebra. -/
theorem finite_center_of_isNoetherian [IsNoetherian S A] :
    Module.Finite S (center R A) := by
  have : Module.Finite S (centerSubmodule S) :=
    Module.Finite.of_fg (IsNoetherian.noetherian (centerSubmodule S))
  exact Module.Finite.equiv (centerSubmoduleEquiv S)

end FiniteOverCentralSubalgebra

section NoetherianCenter

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (S : Subalgebra R (center R A))

/-- The local algebra structure on the ambient algebra for the Noetherian-center theorem. -/
local instance noetherianCenterAlgebra : Algebra S A := centralSubalgebraAlgebra S
/-- The local algebra structure on the center for the Noetherian-center theorem. -/
local instance noetherianCenterCenterAlgebra : Algebra S (center R A) :=
  S.val.toRingHom.toAlgebra

/-- A finite algebra over a Noetherian central subalgebra has Noetherian center. -/
theorem isNoetherianRing_center_of_finite [IsNoetherianRing S] [Module.Finite S A] :
    IsNoetherianRing (center R A) := by
  have hNoetherian : IsNoetherian S A := isNoetherian_of_isNoetherianRing_of_finite S A
  exact @IsNoetherianRing.of_finite S (center R A) _ _ _ _ _
    (@finite_center_of_isNoetherian R A _ _ _ S hNoetherian)

end NoetherianCenter

end Subalgebra

namespace TauCeti

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- An algebra equivalence carries the center onto the center. -/
theorem map_center_eq_center (e : A ≃ₐ[R] B) :
    (Subalgebra.center R A).map (e : A →ₐ[R] B) = Subalgebra.center R B := by
  refine le_antisymm ?_ ?_
  · rintro _ hx
    obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.mp hx
    rw [Subalgebra.mem_center_iff] at ha ⊢
    intro b'
    obtain ⟨a', rfl⟩ := e.surjective b'
    simp only [AlgEquiv.coe_toAlgHom]
    rw [← map_mul, ← map_mul, ha a']
  · intro b hb
    rw [Subalgebra.mem_center_iff] at hb
    refine Subalgebra.mem_map.mpr ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    rw [Subalgebra.mem_center_iff]
    intro a
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hb (e a)

/-- The center of an algebra, transported along an algebra equivalence. -/
def centerCongr (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (map_center_eq_center e))

@[simp]
theorem centerCongr_apply_coe (e : A ≃ₐ[R] B) (x : Subalgebra.center R A) :
    (centerCongr e x : B) = e (x : A) := by
  simp [centerCongr]

/-- The inverse of `centerCongr e` transports the center back along `e.symm`. -/
@[simp]
theorem centerCongr_symm_apply_coe (e : A ≃ₐ[R] B) (y : Subalgebra.center R B) :
    ((centerCongr e).symm y : A) = e.symm (y : B) := by
  apply e.injective
  rw [e.apply_symm_apply, ← centerCongr_apply_coe e, (centerCongr e).apply_symm_apply]

section Pi

variable {ι : Type*} {S : ι → Type*} [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]

/-- The center of a product of algebras is the product of their centers. -/
def centerPiAlgEquiv :
    Subalgebra.center R (Π i, S i) ≃ₐ[R] Π i, Subalgebra.center R (S i) :=
  have mem_iff : ∀ x : Π i, S i,
      x ∈ Subalgebra.center R (Π i, S i) ↔ ∀ i, x i ∈ Subalgebra.center R (S i) := fun _ => by
    rw [Subalgebra.center_pi]; simp
  { toFun := fun x i => ⟨x.1 i, (mem_iff _).mp x.2 i⟩
    invFun := fun y => ⟨fun i => (y i).1, (mem_iff _).mpr fun i => (y i).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }

-- This and `centerPiAlgEquiv_symm_apply_coe` are the defining equations of `centerPiAlgEquiv`:
-- its `toFun` is literally `fun x i => ⟨x.1 i, _⟩` and its `invFun` is `fun y => ⟨fun i => (y i).1,
-- _⟩`, so both sides differ only by the subtype coercion and hold by `rfl`.  The definition is
-- deliberately not `@[expose]`d, so the pre-bump `simp [centerPiAlgEquiv]` has nothing to unfold;
-- the parentheses in `(rfl)` keep the definitional step inside this module, leaving these two
-- lemmas as the whole interface for importers.
@[simp]
theorem centerPiAlgEquiv_apply_coe (x : Subalgebra.center R (Π i, S i)) (i : ι) :
    (centerPiAlgEquiv x i : S i) = (x : Π i, S i) i := (rfl)

/-- The inverse of `centerPiAlgEquiv` assembles a tuple of central elements componentwise. -/
@[simp]
theorem centerPiAlgEquiv_symm_apply_coe (y : Π i, Subalgebra.center R (S i)) (i : ι) :
    (centerPiAlgEquiv.symm y : Π i, S i) i = (y i : S i) := (rfl)

end Pi

section IsCentral

variable (K D : Type*) [Field K] [Semiring D] [Nontrivial D] [Algebra K D]
  [Algebra.IsCentral K D]

/-- The center of a central algebra is the base field. -/
noncomputable def centerAlgEquivOfIsCentral : Subalgebra.center K D ≃ₐ[K] K :=
  (Subalgebra.equivOfEq _ _ (Algebra.IsCentral.center_eq_bot K D)).trans (Algebra.botEquiv K D)

/-- The inverse of `centerAlgEquivOfIsCentral` is the structure map of the algebra. -/
@[simp]
theorem coe_centerAlgEquivOfIsCentral_symm (r : K) :
    ((centerAlgEquivOfIsCentral K D).symm r : D) = algebraMap K D r := by
  simp [centerAlgEquivOfIsCentral]

/-- `centerAlgEquivOfIsCentral` sends a central element to the scalar it is the image of. -/
@[simp]
theorem algebraMap_centerAlgEquivOfIsCentral (x : Subalgebra.center K D) :
    algebraMap K D (centerAlgEquivOfIsCentral K D x) = (x : D) := by
  rw [← coe_centerAlgEquivOfIsCentral_symm, AlgEquiv.symm_apply_apply]

/-- A central algebra has a one-dimensional center. -/
@[simp]
theorem finrank_center_of_isCentral : Module.finrank K (Subalgebra.center K D) = 1 :=
  ((centerAlgEquivOfIsCentral K D).toLinearEquiv.finrank_eq).trans (CommSemiring.finrank_self K)

end IsCentral

/-- A commutative `K`-algebra is central over `K` exactly when its structure map is surjective: the
center of a commutative algebra is all of it, so demanding that the center be the image of `K`
demands that everything be in the image of `K`.

This is the precise sense in which centrality is a strong condition on a field extension: `L / K` is
central only when `L = K`. -/
theorem isCentral_iff_surjective_algebraMap (K D : Type*) [CommSemiring K] [CommSemiring D]
    [Algebra K D] : Algebra.IsCentral K D ↔ Function.Surjective (algebraMap K D) := by
  refine ⟨fun _ x ↦ ?_, fun h ↦ ⟨fun x _ ↦ ?_⟩⟩
  · obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff K).mp
      (Subalgebra.mem_center_iff.mpr fun b ↦ mul_comm b x)
    exact ⟨a, ha.symm⟩
  · obtain ⟨a, rfl⟩ := h x
    exact Algebra.mem_bot.mpr ⟨a, rfl⟩

end TauCeti
