/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.DirectSum

/-!
# Algebra maps out of a graded algebra: the augmentation and scaling

Let `A = (Aₙ)ₙ` be a graded quasicoherent algebra on a scheme `X`, with direct-sum algebra
`⨁ₙ Aₙ`. Algebra maps out of `⨁ₙ Aₙ` are given by their homogeneous components (`descTotal`).
Two families of this kind encode the geometry of the relative spectrum `Spec_X (⨁ₙ Aₙ)`, which is
a cone over `X` when `A` is a cone algebra:

* When the unit `𝒪_X ⟶ A₀` is an isomorphism, the *augmentation* `⨁ₙ Aₙ ⟶ A₀ = 𝒪_X ⟶ B` kills
  every summand of positive degree (`augmentation`). Its relative spectrum is the vertex of the
  cone.
* For a scheme `q : T ⟶ X`, an algebra map `ψ : ⨁ₙ Aₙ ⟶ q_* 𝒪_T` and a global function `c` on
  `T`, multiplying `ψ` by `cⁿ` on the summand `Aₙ` is again an algebra map (`scaleHom`). Read
  through the universal property of relative Spec, this is the contraction action of the affine
  line on the cone: `ψ` is the pullback of functions along a point `t` of the cone, and
  `scaleHom ψ c` is the pullback along `c • t`.

Scaling is an action of the multiplicative monoid `Γ(T, ⊤)` (`scaleHom_one`, `scaleHom_scaleHom`),
scaling by `0` is the augmentation (`scaleHom_zero`), and scaling commutes with pullback of
functions along morphisms over `X` and with morphisms of graded algebras.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.augmentation`: the augmentation
  `⨁ₙ Aₙ ⟶ B`, zero in positive degrees;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.scaleHom`: the algebra map
  `⨁ₙ Aₙ ⟶ q_* 𝒪_T` multiplied by `cⁿ` in degree `n`, characterized by `ιTotal_scaleHom`.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., Appendix B.5 (cones).
* K. Behrend and B. Fantechi, *The intrinsic normal cone*, Invent. Math. 128 (1997), §1.
-/

public section

open CategoryTheory Limits MonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X : Scheme.{u}} (A : GradedQuasicoherentAlgebra X) {B : CommMon X.Modules}

section Augmentation

/-- The components of the augmentation: the inverse of the unit followed by the unit of `B` in
degree zero, and zero in positive degrees. -/
private def augmentationComponent [IsIso A.obj.toMon.one] (B : CommMon X.Modules) :
    ∀ n, A.obj.X n ⟶ B.X
  | 0 => (asIso A.obj.toMon.one).inv ≫ η[B.X]
  | _ + 1 => 0

private theorem augmentationComponent_eq_zero [IsIso A.obj.toMon.one] (B : CommMon X.Modules) :
    ∀ n, n ≠ 0 → augmentationComponent A B n = 0
  | 0, h => absurd rfl h
  | _ + 1, _ => rfl

private theorem augmentationComponent_mul [IsIso A.obj.toMon.one] (B : CommMon X.Modules)
    (i j : ℕ) :
    A.obj.toMon.mul i j ≫ augmentationComponent A B (i + j) =
      (augmentationComponent A B i ⊗ₘ augmentationComponent A B j) ≫ μ[B.X] := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- In degree zero the components are `one⁻¹ ≫ η`, so both sides are determined after
      -- precomposing with the isomorphism `one ⊗ one`; `change` unfolds the components there.
      change A.obj.toMon.mul 0 0 ≫ (asIso A.obj.toMon.one).inv ≫ η[B.X] =
        (((asIso A.obj.toMon.one).inv ≫ η[B.X]) ⊗ₘ
          ((asIso A.obj.toMon.one).inv ≫ η[B.X])) ≫ μ[B.X]
      rw [← cancel_epi (A.obj.toMon.one ⊗ₘ A.obj.toMon.one), tensorHom_comp_tensorHom_assoc]
      simp only [asIso_inv, IsIso.hom_inv_id_assoc]
      rw [tensorHom_def', Category.assoc, Mon.one_mul_assoc]
      simp [unitors_equal]
    · rw [augmentationComponent_eq_zero A B _ (by omega),
        augmentationComponent_eq_zero A B j (by omega)]
      simp only [MonoidalPreadditive.tensor_zero, zero_comp]
      exact comp_zero
  · rw [augmentationComponent_eq_zero A B _ (by omega),
      augmentationComponent_eq_zero A B i (by omega)]
    simp only [MonoidalPreadditive.zero_tensor, zero_comp]
    exact comp_zero

/-- **The augmentation.** If the unit `𝒪_X ⟶ A₀` is an isomorphism, the morphism of commutative
algebras `⨁ₙ Aₙ ⟶ B` which is `A₀ ≅ 𝒪_X ⟶ B` on the summand of degree zero and zero on the
summands of positive degree. For `B = 𝒪_X` it is the projection onto the degree-zero part; its
relative spectrum is the vertex of the cone `Spec_X (⨁ₙ Aₙ)`. -/
def augmentation [IsIso A.obj.toMon.one] (B : CommMon X.Modules) :
    (toQuasicoherentAlgebra.obj A).obj ⟶ B :=
  descTotal A (augmentationComponent A B) (by simp [augmentationComponent])
    (augmentationComponent_mul A B)

/-- The augmentation vanishes on the summands of positive degree. -/
@[simp, reassoc]
theorem ιTotal_augmentation [IsIso A.obj.toMon.one] (B : CommMon X.Modules) (n : ℕ) :
    ιTotal A (n + 1) ≫ (augmentation A B).hom.hom = 0 :=
  ιTotal_descTotal A _ _ _ (n + 1)

/-- **The augmentation is the algebra map killing positive degrees.** A morphism of commutative
algebras `⨁ₙ Aₙ ⟶ B` is the augmentation exactly when it vanishes on every summand of positive
degree. -/
theorem eq_augmentation_iff [IsIso A.obj.toMon.one] (k : (toQuasicoherentAlgebra.obj A).obj ⟶ B) :
    k = augmentation A B ↔ ∀ n, ιTotal A (n + 1) ≫ k.hom.hom = 0 := by
  refine ⟨fun h n ↦ h ▸ ιTotal_augmentation A B n, fun h ↦ commMonHom_ext fun n ↦ ?_⟩
  rw [ιTotal_augmentation]
  exact h n

/-- The augmentation into `B` followed by a morphism of algebras `B ⟶ B'` is the augmentation
into `B'`. -/
@[simp, reassoc]
theorem augmentation_comp [IsIso A.obj.toMon.one] {B' : CommMon X.Modules} (g : B ⟶ B') :
    augmentation A B ≫ g = augmentation A B' :=
  commMonHom_ext fun n ↦ (ιTotal_augmentation_assoc A B n g.hom.hom).trans
    ((zero_comp (C := X.Modules)).trans (ιTotal_augmentation A B' n).symm)

/-- Morphisms of graded algebras commute with the augmentations. -/
@[simp, reassoc]
theorem toQuasicoherentAlgebra_map_comp_augmentation {A' : GradedQuasicoherentAlgebra X}
    [IsIso A.obj.toMon.one] [IsIso A'.obj.toMon.one] (f : A ⟶ A') :
    (toQuasicoherentAlgebra.map f).hom ≫ augmentation A' B = augmentation A B := by
  refine commMonHom_ext fun n ↦ ?_
  -- The composite is typed partly in `SheafOfModules X.ringCatSheaf` and partly in
  -- `X.Modules`, so the reassociation is applied as a term.
  exact (ιTotal_toQuasicoherentAlgebra_map_assoc f (n + 1) _).trans
    ((congrArg (f.hom.hom.hom (n + 1) ≫ ·) (ιTotal_augmentation A' B n)).trans
      ((comp_zero (C := X.Modules)).trans (ιTotal_augmentation A B n).symm))

end Augmentation

section Scaling

variable {T : Scheme.{u}} (q : T ⟶ X)

private theorem scaleHom_one_aux (ψ : (toQuasicoherentAlgebra.obj A).obj ⟶
    q.pushforwardStructureAlgebra) (c : Γ(T, ⊤)) :
    A.obj.toMon.one ≫ ιTotal A 0 ≫ ψ.hom.hom ≫ (Scheme.Modules.pushforward q).map
        (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ 0)) =
      η[q.pushforwardStructureAlgebra.X] := by
  have h₀ : (Scheme.Modules.pushforward q).map
      (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ 0)) = 𝟙 _ := by
    rw [pow_zero, Scheme.Modules.globalSectionsSmul_one]
    exact (Scheme.Modules.pushforward q).map_id _
  -- the goal mixes the `X.Modules` and `SheafOfModules` category instances, on which `rw [h₀]`
  -- cannot build its motive, so `h₀` is applied as a term
  exact (congrArg (fun f ↦ A.obj.toMon.one ≫ ιTotal A 0 ≫ ψ.hom.hom ≫ f) h₀).trans
    ((congrArg (fun f ↦ A.obj.toMon.one ≫ ιTotal A 0 ≫ f) (Category.comp_id _)).trans
      (one_ιTotal_comp A ψ))

private theorem scaleHom_mul_aux (ψ : (toQuasicoherentAlgebra.obj A).obj ⟶
    q.pushforwardStructureAlgebra) (c : Γ(T, ⊤)) (i j : ℕ) :
    A.obj.toMon.mul i j ≫ ιTotal A (i + j) ≫ ψ.hom.hom ≫ (Scheme.Modules.pushforward q).map
        (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ (i + j))) =
      ((ιTotal A i ≫ ψ.hom.hom ≫ (Scheme.Modules.pushforward q).map
          (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ i))) ⊗ₘ
        (ιTotal A j ≫ ψ.hom.hom ≫ (Scheme.Modules.pushforward q).map
          (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ j)))) ≫
        μ[q.pushforwardStructureAlgebra.X] :=
  -- `ψ` is multiplicative on the summands, and the multiplication of `q_* 𝒪_T` turns the
  -- multiplications by `cⁱ` and `cʲ` of the factors into multiplication by `cⁱ * cʲ`; the
  -- composites mix the `X.Modules` and `SheafOfModules` category instances, so the equations are
  -- chained as terms
  (congrArg (fun a ↦ A.obj.toMon.mul i j ≫ ιTotal A (i + j) ≫ ψ.hom.hom ≫
    (Scheme.Modules.pushforward q).map (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) a))
      (pow_add c i j)).trans ((mul_ιTotal_comp_assoc A ψ i j _).trans
        ((congrArg (_ ≫ ·) (Scheme.Hom.pushforward_map_globalSectionsSmul_tensorHom_mul q
          (c ^ i) (c ^ j)).symm).trans ((tensorHom_comp_tensorHom_assoc _ _ _ _ _).trans
            (congrArg (· ≫ μ[q.pushforwardStructureAlgebra.X])
              (congrArg₂ (· ⊗ₘ ·) (Category.assoc _ _ _) (Category.assoc _ _ _))))))

/-- **Scaling an algebra map by a function.** For a scheme `q : T ⟶ X`, a morphism of
algebras `ψ : ⨁ₙ Aₙ ⟶ q_* 𝒪_T` and a global function `c` on `T`, the morphism of algebras
`⨁ₙ Aₙ ⟶ q_* 𝒪_T` which is `ψ` followed by multiplication by `cⁿ` on the summand `Aₙ`. If `ψ`
pulls back regular functions along a point `t : T ⟶ Spec_X (⨁ₙ Aₙ)`, then `scaleHom A q ψ c`
pulls them back along the point `c • t` of the contraction action of the affine line. -/
def scaleHom (ψ : (toQuasicoherentAlgebra.obj A).obj ⟶ q.pushforwardStructureAlgebra)
    (c : Γ(T, ⊤)) : (toQuasicoherentAlgebra.obj A).obj ⟶ q.pushforwardStructureAlgebra :=
  descTotal A (fun n ↦ ιTotal A n ≫ ψ.hom.hom ≫ (Scheme.Modules.pushforward q).map
    (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ n)))
    (scaleHom_one_aux A q ψ c) (scaleHom_mul_aux A q ψ c)

variable (ψ : (toQuasicoherentAlgebra.obj A).obj ⟶ q.pushforwardStructureAlgebra)
  (c : Γ(T, ⊤))

/-- On the summand `Aₙ`, the scaled algebra map `scaleHom A q ψ c` is `ψ` followed by
multiplication by `cⁿ`. -/
@[reassoc]
theorem ιTotal_scaleHom (n : ℕ) :
    ιTotal A n ≫ (scaleHom A q ψ c).hom.hom =
      ιTotal A n ≫ ψ.hom.hom ≫ (Scheme.Modules.pushforward q).map
        (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ n)) :=
  ιTotal_descTotal A _ _ _ n

/-- Scaling by the constant function `1` is the identity. -/
@[simp]
theorem scaleHom_one : scaleHom A q ψ 1 = ψ := by
  refine CommMon.hom_ext _ _ (toQuasicoherentAlgebra_hom_ext fun n ↦ ?_)
  have h₁ : (Scheme.Modules.pushforward q).map
      (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (1 ^ n)) = 𝟙 _ := by
    rw [one_pow, Scheme.Modules.globalSectionsSmul_one]
    exact (Scheme.Modules.pushforward q).map_id _
  exact (ιTotal_scaleHom A q ψ 1 n).trans ((congrArg (fun f ↦ ιTotal A n ≫ ψ.hom.hom ≫ f)
    h₁).trans (congrArg (ιTotal A n ≫ ·) (Category.comp_id _)))

/-- Scaling by `c'` and then by `c` is scaling by `c * c'`. -/
@[simp]
theorem scaleHom_scaleHom (c' : Γ(T, ⊤)) :
    scaleHom A q (scaleHom A q ψ c') c = scaleHom A q ψ (c * c') := by
  refine CommMon.hom_ext _ _ (toQuasicoherentAlgebra_hom_ext fun n ↦ ?_)
  have h : (Scheme.Modules.pushforward q).map
      (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) ((c * c') ^ n)) =
        (Scheme.Modules.pushforward q).map
          (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c' ^ n)) ≫
        (Scheme.Modules.pushforward q).map
          (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ n)) := by
    rw [mul_pow, Scheme.Modules.globalSectionsSmul_mul, Functor.map_comp]
  exact (ιTotal_scaleHom A q _ c n).trans (((ιTotal_scaleHom_assoc A q ψ c' n _).trans
    (congrArg (fun f ↦ ιTotal A n ≫ ψ.hom.hom ≫ f) h.symm)).trans
      (ιTotal_scaleHom A q ψ (c * c') n).symm)

/-- Scaling by the function `0` is the augmentation: it kills every summand of positive
degree. -/
theorem scaleHom_zero [IsIso A.obj.toMon.one] :
    scaleHom A q ψ 0 = augmentation A q.pushforwardStructureAlgebra := by
  refine commMonHom_ext fun n ↦ ?_
  have h₀ : (Scheme.Modules.pushforward q).map
      (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) ((0 : Γ(T, ⊤)) ^ (n + 1))) = 0 := by
    rw [zero_pow n.succ_ne_zero, Scheme.Modules.globalSectionsSmul_zero, Functor.map_zero]
  rw [ιTotal_augmentation]
  exact (ιTotal_scaleHom A q ψ 0 (n + 1)).trans ((congrArg (fun f ↦ ιTotal A (n + 1) ≫
    ψ.hom.hom ≫ f) h₀).trans ((congrArg (ιTotal A (n + 1) ≫ ·) (comp_zero (C := X.Modules))).trans
      (comp_zero (C := X.Modules))))

/-- Scaling the augmentation by any function leaves it unchanged. -/
@[simp]
theorem scaleHom_augmentation [IsIso A.obj.toMon.one] :
    scaleHom A q (augmentation A q.pushforwardStructureAlgebra) c =
      augmentation A q.pushforwardStructureAlgebra := by
  refine commMonHom_ext fun n ↦ ?_
  rw [ιTotal_augmentation]
  exact (ιTotal_scaleHom A q _ c (n + 1)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (ιTotal_augmentation A _ n)).trans (zero_comp (C := X.Modules))))

/-- Scaling commutes with pullback of functions along a morphism `g : V ⟶ T` over `X`, which
pulls back the scalar `c` to `g^♯ c`. -/
theorem scaleHom_comp_pushforwardStructureAlgebraMap {V : Scheme.{u}} {p : V ⟶ X} (g : V ⟶ T)
    (h : g ≫ q = p) :
    scaleHom A q ψ c ≫ Scheme.Hom.pushforwardStructureAlgebraMap g h =
      scaleHom A p (ψ ≫ Scheme.Hom.pushforwardStructureAlgebraMap g h) (g.appTop c) := by
  refine CommMon.hom_ext _ _ (toQuasicoherentAlgebra_hom_ext fun n ↦ ?_)
  have e : g.appTop (c ^ n) = g.appTop c ^ n := map_pow _ _ _
  refine ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (ιTotal_scaleHom A q ψ c n)).trans
    ?_)).trans (ιTotal_scaleHom A p _ (g.appTop c) n).symm
  -- pulling back along `g` turns multiplication by `cⁿ` into multiplication by `(g^♯ c)ⁿ`; the
  -- composites mix the `X.Modules` and `SheafOfModules` category instances, so the
  -- reassociations are applied as terms
  exact (Category.assoc _ _ _).trans (congrArg (ιTotal A n ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (ψ.hom.hom ≫ ·) (Scheme.Hom.globalSectionsSmul_pushforwardStructureAlgebraMap g h
      (c ^ n))).trans ((Category.assoc _ _ _).symm.trans (congrArg (fun a ↦ _ ≫
        (Scheme.Modules.pushforward p).map (Scheme.Modules.globalSectionsSmul (𝟙_ V.Modules) a))
          e)))))

/-- Scaling commutes with morphisms of graded algebras. -/
theorem toQuasicoherentAlgebra_map_comp_scaleHom {A' : GradedQuasicoherentAlgebra X}
    (f : A ⟶ A') (ψ' : (toQuasicoherentAlgebra.obj A').obj ⟶ q.pushforwardStructureAlgebra) :
    (toQuasicoherentAlgebra.map f).hom ≫ scaleHom A' q ψ' c =
      scaleHom A q ((toQuasicoherentAlgebra.map f).hom ≫ ψ') c := by
  refine CommMon.hom_ext _ _ (toQuasicoherentAlgebra_hom_ext fun n ↦ ?_)
  -- both sides are `fₙ` followed by the restriction of `ψ'` to `A'ₙ` and multiplication by `cⁿ`
  have h₁ := ιTotal_toQuasicoherentAlgebra_map_assoc f n (scaleHom A' q ψ' c).hom.hom
  have h₂ := ιTotal_toQuasicoherentAlgebra_map_assoc f n (ψ'.hom.hom ≫
    (Scheme.Modules.pushforward q).map (Scheme.Modules.globalSectionsSmul (𝟙_ T.Modules) (c ^ n)))
  have h₃ := ιTotal_scaleHom A q ((toQuasicoherentAlgebra.map f).hom ≫ ψ') c n
  have h₄ := ιTotal_scaleHom A' q ψ' c n
  exact h₁.trans ((congrArg (f.hom.hom.hom n ≫ ·) h₄).trans (h₂.symm.trans
    ((congrArg (ιTotal A n ≫ ·) (Category.assoc _ _ _).symm).trans h₃.symm)))

end Scaling

end GradedQuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
