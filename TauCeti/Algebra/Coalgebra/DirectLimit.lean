/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Directed colimits of coalgebras

Let `(Cᵢ, fᵢⱼ)` be a directed system of `R`-coalgebras with coalgebra morphisms as transition
maps. Its colimit as modules, `Module.DirectLimit C f`, is again a coalgebra: the
comultiplication and the counit are the unique linear maps with
`Δ (ofᵢ c) = (ofᵢ ⊗ ofᵢ) (Δ c)` and `ε (ofᵢ c) = ε c`. The canonical maps are then coalgebra
morphisms, and a compatible family of coalgebra morphisms out of the stages induces a coalgebra
morphism out of the colimit.

The transition maps need not be injective, so the colimit is not in general a union of
subcoalgebras of a fixed coalgebra. This is the situation of the coalgebra reconstructed from a
fibre functor, the colimit of the duals of the finite-dimensional algebras of endomorphisms of
the fibre functor on finite pieces of the category; see Deligne–Milne, *Tannakian categories*,
proof of Proposition 2.14, and Huber–Müller-Stach, *Periods and Nori motives*, §7.1.

## Main definitions

* `Module.DirectLimit.instCoalgebra`: the coalgebra structure on the colimit.
* `Module.DirectLimit.ofCoalgHom`: the canonical map from a stage, as a coalgebra morphism.
* `Module.DirectLimit.liftCoalgHom`: the coalgebra morphism out of the colimit induced by a
  compatible family of coalgebra morphisms.
-/

public section

open TensorProduct Coalgebra

namespace Module.DirectLimit

variable {R : Type*} [CommSemiring R] {ι : Type*} [Preorder ι] [DecidableEq ι]
  {C : ι → Type*} [∀ i, AddCommMonoid (C i)] [∀ i, Module R (C i)] [∀ i, Coalgebra R (C i)]
  (f : ∀ i j, i ≤ j → C i →ₗc[R] C j)

/-- The comultiplication and counit of a directed colimit of coalgebras. -/
noncomputable instance instCoalgebraStruct :
    CoalgebraStruct R (DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) where
  comul := lift R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j))
    (fun i ↦ TensorProduct.map (of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i)
      (of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i) ∘ₗ comul)
    fun i j h x ↦ by
      have hof : of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) j ∘ₗ
          (f i j h : C i →ₗ[R] C j) = of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i :=
        LinearMap.ext fun _ ↦ of_f
      simp only [LinearMap.comp_apply, CoalgHom.coe_linearMapOfClass]
      rw [← CoalgHomClass.map_comp_comul_apply, TensorProduct.map_map, hof]
  counit := lift R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) (fun _ ↦ counit)
    fun i j h x ↦ LinearMap.congr_fun (CoalgHomClass.counit_comp (f i j h)) x

/-- The comultiplication of the colimit on the image of a stage. -/
@[simp]
theorem comul_of (i : ι) (x : C i) :
    comul (R := R) (of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i x) =
      TensorProduct.map (of R ι C _ i) (of R ι C _ i) (comul x) :=
  lift_of ..

/-- The counit of the colimit on the image of a stage. -/
@[simp]
theorem counit_of (i : ι) (x : C i) :
    counit (R := R) (of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i x) = counit x :=
  lift_of ..

/-- The canonical map of a stage commutes with the comultiplications. -/
theorem comul_comp_of (i : ι) :
    comul (R := R) ∘ₗ of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i =
      TensorProduct.map (of R ι C _ i) (of R ι C _ i) ∘ₗ comul :=
  LinearMap.ext (comul_of f i)

/-- The canonical map of a stage commutes with the counits. -/
theorem counit_comp_of (i : ι) :
    counit (R := R) ∘ₗ of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i = counit :=
  LinearMap.ext (counit_of f i)

/-- A directed colimit of coalgebras along coalgebra morphisms is a coalgebra. -/
-- The proof is adapted from Mathlib's coalgebra instance on a quotient by a coideal, in
-- `Mathlib/RingTheory/Coalgebra/Quotient.lean`.
noncomputable instance instCoalgebra :
    Coalgebra R (DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) := by
  constructor <;> ext i : 1 <;> simp only [coassoc_simps, comul_comp_of, counit_comp_of]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

/-- The canonical map from a stage into a directed colimit of coalgebras, as a coalgebra
morphism. -/
noncomputable def ofCoalgHom (i : ι) :
    C i →ₗc[R] DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j) where
  __ := of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i
  counit_comp := counit_comp_of f i
  map_comp_comul := (comul_comp_of f i).symm

@[simp]
theorem ofCoalgHom_apply (i : ι) (x : C i) :
    ofCoalgHom f i x = of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i x := by
  rfl

@[simp]
theorem toLinearMap_ofCoalgHom (i : ι) :
    (ofCoalgHom f i : C i →ₗ[R] _) = of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i := by
  rfl

/-- The canonical coalgebra morphisms are compatible with the transition maps. -/
@[simp]
theorem ofCoalgHom_comp {i j : ι} (h : i ≤ j) :
    (ofCoalgHom f j).comp (f i j h) = ofCoalgHom f i :=
  CoalgHom.ext fun _ ↦ of_f

variable {D : Type*} [AddCommMonoid D] [Module R D] [Coalgebra R D]
  (g : ∀ i, C i →ₗc[R] D) (hg : ∀ i j h, (g j).comp (f i j h) = g i)

/-- The universal property of a directed colimit of coalgebras: a compatible family of coalgebra
morphisms out of the stages induces a coalgebra morphism out of the colimit. -/
noncomputable def liftCoalgHom :
    (DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) →ₗc[R] D where
  __ := lift R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) (fun i ↦ (g i : C i →ₗ[R] D))
    -- `by simpa` states the compatibility with the linear coercions that `lift` expects.
    fun i j h x ↦ by simpa using CoalgHom.congr_fun (hg i j h) x
  counit_comp := hom_ext fun i ↦ LinearMap.ext fun x ↦ by
    simp only [LinearMap.comp_apply, lift_of, counit_of]
    exact CoalgHomClass.counit_comp_apply (g i) x
  map_comp_comul := hom_ext fun i ↦ LinearMap.ext fun x ↦ by
    simp only [LinearMap.comp_apply, lift_of, comul_of, CoalgHom.coe_linearMapOfClass]
    rw [← CoalgHomClass.map_comp_comul_apply (g i)]
    induction comul (R := R) x using TensorProduct.inductionOn with
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]

@[simp]
theorem liftCoalgHom_of (i : ι) (x : C i) :
    liftCoalgHom f g hg (of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i x) = g i x := by
  simp [liftCoalgHom]

@[simp]
theorem liftCoalgHom_comp_ofCoalgHom (i : ι) :
    (liftCoalgHom f g hg).comp (ofCoalgHom f i) = g i :=
  CoalgHom.ext fun x ↦ liftCoalgHom_of f g hg i x

/-- Coalgebra morphisms out of a directed colimit of coalgebras agree when they agree on every
stage. -/
@[ext]
theorem coalgHom_ext {φ ψ : (DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) →ₗc[R] D}
    (h : ∀ i, φ.comp (ofCoalgHom f i) = ψ.comp (ofCoalgHom f i)) : φ = ψ := by
  refine CoalgHom.linearMapOfClass_injective (hom_ext fun i ↦ ?_)
  exact congr((↑$(h i) : C i →ₗ[R] D))

end Module.DirectLimit
