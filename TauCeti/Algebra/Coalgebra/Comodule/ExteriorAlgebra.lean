/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.RingTheory.GradedAlgebra.DecomposeTensor
public import TauCeti.RingTheory.TensorProduct.SquareZero

/-!
# The exterior algebra of a comodule

Let `H` be a commutative bialgebra over a commutative ring `R` and `M` a right `H`-comodule.
The exterior algebra `ExteriorAlgebra R M` is again a right `H`-comodule, with the coaction
determined multiplicatively by that of `M`: in Sweedler notation `m ↦ m₍₀₎ ⊗ m₍₁₎`,

`ι m₁ * ⋯ * ι mₙ ↦ ∏ᵢ (ι mᵢ₍₀₎ ⊗ mᵢ₍₁₎)`.

Since `H` is commutative, `ExteriorAlgebra R M ⊗[R] H` is an algebra in which the image of the
coaction of `M` still squares to zero, so the coaction extends to an algebra homomorphism
`exteriorAlgebraCoact : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M ⊗[R] H`; the comodule laws
then hold because they hold on generators. This coaction preserves the exterior grading, so
every exterior power `⋀[R]^n M` is a subcomodule. The points of `H` act on the scalar extension
of the exterior algebra by algebra endomorphisms, compatibly with their action on `M` through the
comodule morphism `Hom.exteriorAlgebraι` (by `baseChange_comp_endOfPoint`).

For an affine group `G = Spec H` with a representation `M`, this is the representation of `G`
on `⋀ M` and its homogeneous pieces. Chevalley's theorem realizing a closed subgroup as the
stabilizer of a line uses the line spanned by the top exterior product of a subrepresentation.

Following `Comodule.tensor`, `Comodule.exteriorAlgebra` is not a global instance.

## Main declarations

* `TauCeti.Comodule.exteriorAlgebraCoact`: the coaction of the exterior algebra, as an algebra
  homomorphism.
* `TauCeti.Comodule.exteriorAlgebra`: the right `H`-comodule structure on `ExteriorAlgebra R M`.
* `TauCeti.Comodule.Hom.exteriorAlgebraι` and `TauCeti.Comodule.Hom.exteriorAlgebraMap`: the
  inclusion of generators and the functoriality of the exterior algebra, as comodule morphisms.
* `TauCeti.Comodule.exteriorAlgebraCoact_mem_decomposeTensor`: the coaction preserves degrees.
* `TauCeti.Comodule.exteriorPowerSubcomodule`: the exterior power `⋀[R]^n M` as a subcomodule.
* `TauCeti.Comodule.exteriorAlgebraEndOfPoint`: the action of a point on the scalar extension
  of the exterior algebra, as an algebra homomorphism.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

variable {R H M N P : Type*} [CommRing R] [CommSemiring H] [Bialgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]
  [AddCommGroup N] [Module R N] [Comodule R H N]
  [AddCommGroup P] [Module R P] [Comodule R H P]

variable (R H M) in
/-- The coaction of the exterior algebra of a comodule, as an algebra homomorphism: it sends a
generator `ι m` to `ι m₍₀₎ ⊗ m₍₁₎`, the coaction of `m` followed by the inclusion of generators. -/
noncomputable def exteriorAlgebraCoact :
    ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M ⊗[R] H :=
  ExteriorAlgebra.lift R
    ⟨(ExteriorAlgebra.ι R).rTensor H ∘ₗ coact (R := R) (C := H) (M := M), fun _ ↦
      (ExteriorAlgebra.ι R).rTensor_mul_self_eq_zero (fun m ↦ ExteriorAlgebra.ι_sq_zero m) _⟩

@[simp]
theorem exteriorAlgebraCoact_ι (m : M) :
    exteriorAlgebraCoact R H M (ExteriorAlgebra.ι R m) =
      (ExteriorAlgebra.ι R).rTensor H (coact (R := R) (C := H) m) :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

omit [Comodule R H M] in
/-- An algebra homomorphism on `H` commutes with the inclusion of generators. -/
private theorem map_id_rTensor_ι {K : Type*} [Semiring K] [Algebra R K] (φ : H →ₐ[R] K)
    (z : M ⊗[R] H) :
    Algebra.TensorProduct.map (AlgHom.id R (ExteriorAlgebra R M)) φ
        ((ExteriorAlgebra.ι R).rTensor H z) =
      (ExteriorAlgebra.ι R).rTensor K (φ.toLinearMap.lTensor M z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m h => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Coassociativity of `exteriorAlgebraCoact`, as an equality of algebra homomorphisms. -/
private theorem exteriorAlgebraCoact_coassoc_algHom :
    (Algebra.TensorProduct.assoc R R R (ExteriorAlgebra R M) H H).toAlgHom.comp
        ((Algebra.TensorProduct.map (exteriorAlgebraCoact R H M) (AlgHom.id R H)).comp
          (exteriorAlgebraCoact R H M)) =
      (Algebra.TensorProduct.map (AlgHom.id R (ExteriorAlgebra R M))
        (Bialgebra.comulAlgHom R H)).comp (exteriorAlgebraCoact R H M) := by
  apply ExteriorAlgebra.hom_ext
  ext m
  have hassoc (z : M ⊗[R] H) :
      Algebra.TensorProduct.assoc R R R (ExteriorAlgebra R M) H H
          (Algebra.TensorProduct.map (exteriorAlgebraCoact R H M) (AlgHom.id R H)
            ((ExteriorAlgebra.ι R).rTensor H z)) =
        (ExteriorAlgebra.ι R).rTensor (H ⊗[R] H)
          (TensorProduct.assoc R M H H ((coact (R := R) (C := H) (M := M)).rTensor H z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul m h =>
      simp only [LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, exteriorAlgebraCoact_ι,
        AlgHom.coe_id, id_eq]
      induction coact (R := R) (C := H) m using TensorProduct.inductionOn with
      | tmul n k => simp
      | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom, exteriorAlgebraCoact_ι, hassoc, coassoc_apply,
    map_id_rTensor_ι, Bialgebra.toLinearMap_comulAlgHom]

/-- Coassociativity of the coaction of the exterior algebra. -/
theorem exteriorAlgebraCoact_coassoc :
    TensorProduct.assoc R (ExteriorAlgebra R M) H H ∘ₗ
        (exteriorAlgebraCoact R H M).toLinearMap.rTensor H ∘ₗ
          (exteriorAlgebraCoact R H M).toLinearMap =
      Coalgebra.comul.lTensor (ExteriorAlgebra R M) ∘ₗ
        (exteriorAlgebraCoact R H M).toLinearMap := by
  have h := congrArg AlgHom.toLinearMap (exteriorAlgebraCoact_coassoc_algHom (R := R) (H := H)
    (M := M))
  rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq, TensorProduct.AlgebraTensorModule.map_eq,
    AlgHom.toLinearMap_id, AlgHom.toLinearMap_id, ← LinearMap.rTensor_def, ← LinearMap.lTensor_def,
    Bialgebra.toLinearMap_comulAlgHom, AlgEquiv.toAlgHom_toLinearMap,
    Algebra.TensorProduct.assoc_toLinearEquiv, TensorProduct.AlgebraTensorModule.assoc_eq] at h
  exact h

/-- The counit law for the coaction of the exterior algebra. -/
theorem exteriorAlgebraCoact_counit :
    Coalgebra.counit.lTensor (ExteriorAlgebra R M) ∘ₗ (exteriorAlgebraCoact R H M).toLinearMap =
      (TensorProduct.mk R (ExteriorAlgebra R M) R).flip 1 := by
  have h : (Algebra.TensorProduct.map (AlgHom.id R (ExteriorAlgebra R M))
      (Bialgebra.counitAlgHom R H)).comp (exteriorAlgebraCoact R H M) =
      Algebra.TensorProduct.includeLeft := by
    apply ExteriorAlgebra.hom_ext
    ext m
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, exteriorAlgebraCoact_ι, map_id_rTensor_ι,
      Bialgebra.toLinearMap_counitAlgHom, lTensor_counit_coact, LinearMap.rTensor_tmul,
      Algebra.TensorProduct.includeLeft_apply]
  have h' := congrArg AlgHom.toLinearMap h
  rw [AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq, AlgHom.toLinearMap_id, ← LinearMap.lTensor_def,
    Bialgebra.toLinearMap_counitAlgHom] at h'
  rw [h']
  ext x
  simp

variable (R H M) in
/-- The exterior algebra of a right comodule over a commutative bialgebra, with the
multiplicative coaction `exteriorAlgebraCoact`.

Following `Comodule.tensor`, this is deliberately *not* a global instance. Select it explicitly,
or register it as a local instance. -/
@[expose, implicit_reducible]
noncomputable def exteriorAlgebra : Comodule R H (ExteriorAlgebra R M) where
  coact := (exteriorAlgebraCoact R H M).toLinearMap
  coassoc := exteriorAlgebraCoact_coassoc
  lTensor_counit_comp_coact := exteriorAlgebraCoact_counit

attribute [local instance] exteriorAlgebra

/-- The coaction of the exterior-algebra comodule is `exteriorAlgebraCoact`. -/
@[simp]
theorem exteriorAlgebra_coact :
    coact (R := R) (C := H) (M := ExteriorAlgebra R M) =
      (exteriorAlgebraCoact R H M).toLinearMap :=
  rfl

namespace Hom

variable (R H M) in
/-- The inclusion `ι : M → ExteriorAlgebra R M` of generators, as a comodule morphism. -/
noncomputable def exteriorAlgebraι : Hom R H M (ExteriorAlgebra R M) where
  toLinearMap := ExteriorAlgebra.ι R
  map_coact := by
    ext m
    simp [LinearMap.rTensor_def]

@[simp]
theorem exteriorAlgebraι_toLinearMap :
    (exteriorAlgebraι R H M).toLinearMap = ExteriorAlgebra.ι R :=
  (rfl)

@[simp]
theorem exteriorAlgebraι_apply (m : M) :
    exteriorAlgebraι R H M m = ExteriorAlgebra.ι R m :=
  (rfl)

/-- The algebra homomorphism `ExteriorAlgebra.map f` induced by a comodule morphism commutes
with the coactions. -/
private theorem exteriorAlgebraCoact_comp_map (f : Hom R H M N) :
    (Algebra.TensorProduct.map (ExteriorAlgebra.map f.toLinearMap) (AlgHom.id R H)).comp
        (exteriorAlgebraCoact R H M) =
      (exteriorAlgebraCoact R H N).comp (ExteriorAlgebra.map f.toLinearMap) := by
  apply ExteriorAlgebra.hom_ext
  ext m
  have hmap (z : M ⊗[R] H) :
      Algebra.TensorProduct.map (ExteriorAlgebra.map f.toLinearMap) (AlgHom.id R H)
          ((ExteriorAlgebra.ι R).rTensor H z) =
        (ExteriorAlgebra.ι R).rTensor H (TensorProduct.map f.toLinearMap LinearMap.id z) := by
    induction z using TensorProduct.inductionOn with
    | tmul m h => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, exteriorAlgebraCoact_ι, hmap, Hom.map_coact_apply,
    ExteriorAlgebra.map_apply_ι, Hom.coe_toLinearMap]

/-- The map of exterior algebras induced by a comodule morphism, as a comodule morphism. -/
noncomputable def exteriorAlgebraMap (f : Hom R H M N) :
    Hom R H (ExteriorAlgebra R M) (ExteriorAlgebra R N) where
  toLinearMap := (ExteriorAlgebra.map f.toLinearMap).toLinearMap
  map_coact := by
    have h := congrArg AlgHom.toLinearMap (exteriorAlgebraCoact_comp_map f)
    rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq, AlgHom.toLinearMap_id] at h
    rw [exteriorAlgebra_coact, exteriorAlgebra_coact]
    exact h

@[simp]
theorem exteriorAlgebraMap_toLinearMap (f : Hom R H M N) :
    (exteriorAlgebraMap f).toLinearMap = (ExteriorAlgebra.map f.toLinearMap).toLinearMap :=
  (rfl)

@[simp]
theorem exteriorAlgebraMap_apply (f : Hom R H M N) (x : ExteriorAlgebra R M) :
    exteriorAlgebraMap f x = ExteriorAlgebra.map f.toLinearMap x :=
  (rfl)

/-- The exterior-algebra functor on comodules preserves identities. -/
theorem exteriorAlgebraMap_id : exteriorAlgebraMap (id R H M) = id R H (ExteriorAlgebra R M) := by
  apply toLinearMap_injective
  rw [exteriorAlgebraMap_toLinearMap, id_toLinearMap, id_toLinearMap, ExteriorAlgebra.map_id,
    AlgHom.toLinearMap_id]

/-- The exterior-algebra functor on comodules preserves composition. -/
theorem exteriorAlgebraMap_comp (g : Hom R H N P) (f : Hom R H M N) :
    exteriorAlgebraMap (g.comp f) = (exteriorAlgebraMap g).comp (exteriorAlgebraMap f) := by
  apply toLinearMap_injective
  rw [comp_toLinearMap, exteriorAlgebraMap_toLinearMap, exteriorAlgebraMap_toLinearMap,
    exteriorAlgebraMap_toLinearMap, comp_toLinearMap, ← ExteriorAlgebra.map_comp_map,
    AlgHom.comp_toLinearMap]

/-- The exterior-algebra functor is compatible with the inclusion of generators. -/
@[simp]
theorem exteriorAlgebraMap_comp_exteriorAlgebraι (f : Hom R H M N) :
    (exteriorAlgebraMap f).comp (exteriorAlgebraι R H M) = (exteriorAlgebraι R H N).comp f := by
  ext m
  simp

end Hom

section ExteriorPower

/-- The coaction of the exterior algebra preserves the exterior grading: it maps `⋀[R]^n M` into
the image of `⋀[R]^n M ⊗[R] H`. -/
theorem exteriorAlgebraCoact_mem_decomposeTensor {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) :
    exteriorAlgebraCoact R H M x ∈ DirectSum.decomposeTensor (fun i : ℕ ↦ ⋀[R]^i M) H n := by
  have hι (z : M ⊗[R] H) : (ExteriorAlgebra.ι R).rTensor H z ∈
      DirectSum.decomposeTensor (fun i : ℕ ↦ ⋀[R]^i M) H 1 := by
    induction z using TensorProduct.inductionOn with
    | tmul m h =>
      exact DirectSum.tmul_mem_decomposeTensor
        (by simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι R) m) h
    | add x y hx hy => exact map_add (ExteriorAlgebra.ι R |>.rTensor H) x y ▸ add_mem hx hy
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (SetLike.one_mem_graded _)
  | add x y i _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, exteriorAlgebraCoact_ι, Nat.succ_eq_one_add]
    exact SetLike.mul_mem_graded (hι _) hx

variable (R H M) in
/-- The exterior power `⋀[R]^n M` as a subcomodule of the exterior algebra. -/
noncomputable def exteriorPowerSubcomodule (n : ℕ) : Subcomodule R H (ExteriorAlgebra R M) :=
  Subcomodule.ofSubmodule (⋀[R]^n M) fun _ hx ↦ by
    rw [exteriorAlgebra_coact, AlgHom.toLinearMap_apply, ← LinearMap.rTensor_def,
      ← DirectSum.decomposeTensor_apply]
    exact exteriorAlgebraCoact_mem_decomposeTensor hx

@[simp]
theorem exteriorPowerSubcomodule_toSubmodule (n : ℕ) :
    (exteriorPowerSubcomodule R H M n).toSubmodule = ⋀[R]^n M :=
  (rfl)

@[simp]
theorem mem_exteriorPowerSubcomodule {n : ℕ} {x : ExteriorAlgebra R M} :
    x ∈ exteriorPowerSubcomodule R H M n ↔ x ∈ ⋀[R]^n M :=
  Iff.rfl

end ExteriorPower

section Points

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- The action of an `A`-point `g` of `H` on the scalar extension `A ⊗[R] ExteriorAlgebra R M`,
as an `A`-algebra homomorphism. Its underlying linear map is `endOfPoint`
(`exteriorAlgebraEndOfPoint_toLinearMap`), so points act on the exterior algebra
multiplicatively. -/
noncomputable def exteriorAlgebraEndOfPoint (g : H →ₐ[R] A) :
    A ⊗[R] ExteriorAlgebra R M →ₐ[A] A ⊗[R] ExteriorAlgebra R M :=
  Algebra.TensorProduct.lift (Algebra.ofId A _)
    ((Algebra.TensorProduct.comm R (ExteriorAlgebra R M) A).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R (ExteriorAlgebra R M)) g).comp
        (exteriorAlgebraCoact R H M)))
    fun a _ ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left a _

/-- The algebra homomorphism `exteriorAlgebraEndOfPoint g` is the action `endOfPoint` of the
point `g` on the exterior-algebra comodule. -/
theorem exteriorAlgebraEndOfPoint_toLinearMap (g : H →ₐ[R] A) :
    (exteriorAlgebraEndOfPoint (M := M) g).toLinearMap = endOfPoint (ExteriorAlgebra R M) g := by
  apply LinearMap.restrictScalars_injective R
  refine TensorProduct.ext' fun a x ↦ ?_
  have hcomm (z : ExteriorAlgebra R M ⊗[R] H) :
      Algebra.TensorProduct.comm R (ExteriorAlgebra R M) A
          (Algebra.TensorProduct.map (AlgHom.id R (ExteriorAlgebra R M)) g z) =
        TensorProduct.comm R (ExteriorAlgebra R M) A (g.toLinearMap.lTensor _ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul y h => simp
    | add z w hz hw => simp only [map_add, hz, hw]
  simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, exteriorAlgebraEndOfPoint,
    Algebra.TensorProduct.lift_tmul, endOfPoint_tmul, exteriorAlgebra_coact, Algebra.ofId_apply,
    ← Algebra.smul_def, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hcomm]

@[simp]
theorem exteriorAlgebraEndOfPoint_apply (g : H →ₐ[R] A) (x : A ⊗[R] ExteriorAlgebra R M) :
    exteriorAlgebraEndOfPoint g x = endOfPoint (ExteriorAlgebra R M) g x := by
  rw [← AlgHom.toLinearMap_apply, exteriorAlgebraEndOfPoint_toLinearMap]

/-- Points fix the unit of the scalar extension of the exterior algebra. -/
theorem endOfPoint_exteriorAlgebra_one (g : H →ₐ[R] A) :
    endOfPoint (ExteriorAlgebra R M) g 1 = 1 := by
  rw [← exteriorAlgebraEndOfPoint_apply, map_one]

/-- Points act on the scalar extension of the exterior algebra multiplicatively. -/
theorem endOfPoint_exteriorAlgebra_mul (g : H →ₐ[R] A) (x y : A ⊗[R] ExteriorAlgebra R M) :
    endOfPoint (ExteriorAlgebra R M) g (x * y) =
      endOfPoint (ExteriorAlgebra R M) g x * endOfPoint (ExteriorAlgebra R M) g y := by
  simp only [← exteriorAlgebraEndOfPoint_apply, map_mul]

end Points

end Comodule

end TauCeti
