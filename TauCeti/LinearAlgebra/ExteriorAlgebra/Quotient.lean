/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.Subalgebra.Centralizer

/-!
# Factoring maps through exterior algebras of quotients

An algebra homomorphism from an exterior algebra descends to the exterior algebra of a module
quotient when it kills the one-forms coming from the submodule. The map may be linear over a
smaller base ring, in which case the coefficient ring acts on the centralizer of its image.
-/

public section

namespace AlgHom

variable {R B M P : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
  [Ring P] [Algebra R P]

/-- An algebra map from an exterior algebra that kills the generators in a submodule factors
through the exterior algebra of the quotient. -/
def factorExteriorAlgebraQuotient (F : ExteriorAlgebra B M →ₐ[R] P) (N : Submodule B M)
    (hF : ∀ m ∈ N, F (ExteriorAlgebra.ι B m) = 0) :
    { G : ExteriorAlgebra B (M ⧸ N) →ₐ[R] P //
      ∀ ω, G (ExteriorAlgebra.map N.mkQ ω) = F ω } := by
  let f := F.comp (IsScalarTower.toAlgHom R B (ExteriorAlgebra B M))
  let S := Subalgebra.centralizer R (Set.range f)
  letI : Algebra B S := f.centralizerRangeAlgebra
  letI : IsScalarTower R B S := f.centralizerRangeIsScalarTower
  have hS (b : B) : (algebraMap B S b : P) = f b := f.coe_algebraMap_centralizerRange b
  have hi (m : M) : F (ExteriorAlgebra.ι B m) ∈ S := by
    apply (Subalgebra.mem_centralizer_iff R).mpr
    rintro _ ⟨b, rfl⟩
    simpa only [f, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, map_mul] using
      congrArg F (Algebra.commutes b (ExteriorAlgebra.ι B m))
  let L : M →ₗ[B] S :=
    { toFun := fun m ↦ ⟨F (ExteriorAlgebra.ι B m), hi m⟩
      map_add' := fun x y ↦ Subtype.ext <| by simp
      map_smul' := fun b m ↦ Subtype.ext <| by simp [Algebra.smul_def, hS, f] }
  have hN : N ≤ LinearMap.ker L := by
    intro m hm
    exact LinearMap.mem_ker.mpr (Subtype.ext (hF m hm))
  let L' : (M ⧸ N) →ₗ[B] S := N.liftQ L hN
  have hL (m : M) : L' (N.mkQ m) = L m := Submodule.liftQ_apply N L m
  have hsq (m : M ⧸ N) : L' m * L' m = 0 := by
    obtain ⟨m, rfl⟩ := N.mkQ_surjective m
    rw [hL]
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_zero]
    exact (map_mul F _ _).symm.trans (by rw [ExteriorAlgebra.ι_sq_zero, map_zero])
  let G := ExteriorAlgebra.lift B ⟨L', hsq⟩
  refine ⟨S.val.comp (G.restrictScalars R), ?_⟩
  intro ω
  induction ω using ExteriorAlgebra.induction with
  | algebraMap b =>
    rw [AlgHom.commutes, AlgHom.comp_apply, AlgHom.coe_restrictScalars', AlgHom.commutes]
    exact hS b
  | ι m =>
    rw [ExteriorAlgebra.map_apply_ι, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
      ExteriorAlgebra.lift_ι_apply, hL]
    exact Subalgebra.val_apply _ _
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgHom
