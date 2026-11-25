/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange

/-!
# Functoriality of the projective `K₀` of a ring

A ring homomorphism `f : R →+* S` of possibly noncommutative rings induces a homomorphism

```text
K₀(f) : K₀(R) →+ K₀(S),   [P] ↦ [P ⊗_R S],
```

of the projective `K₀`-groups of finitely generated projective right modules
(`TauCeti.KZero`). A right `R`-module is a left `Rᵐᵒᵖ`-module, and `P ⊗_R S` is the balanced
extension of scalars `Sᵐᵒᵖ ⊗_{Rᵐᵒᵖ} P` along `fᵐᵒᵖ : Rᵐᵒᵖ →+* Sᵐᵒᵖ`; extension of scalars
preserves finitely generated projective modules without any flatness hypothesis, and it is
additive, so it descends to split Grothendieck groups. The construction is covariantly functorial:
`K₀(id) = id` and `K₀(g ∘ f) = K₀(g) ∘ K₀(f)`. The composition law comes from the natural
isomorphism `RingHom.finiteProjectiveModulesExtendScalarsCompIso` comparing the two ways of
extending around a commuting square of ring homomorphisms; this isomorphism also glues the two
extensions of a module over a fibre product of rings in Milnor's patching construction.

On generators, `K₀(f)` sends the free module of rank one `[R]` to `[S]`, and in the idempotent
description of `K₀` (`TauCeti.IdempotentMonoid.kZeroEquiv`) it applies `f` to the entries: the
class `[eRⁿ]` of the image of an idempotent matrix `e` goes to the class `[f(e)Sⁿ]`.

## Main definitions

* `TauCeti.KZero.map f`: the homomorphism `K₀(R) →+ K₀(S)` induced by a ring homomorphism `f`.

## Main results

* `TauCeti.KZero.map_of_linearEquiv`: `K₀(f)` sends `[P]` to the class of any module isomorphic to
  `P ⊗_R S`.
* `TauCeti.KZero.map_id`, `TauCeti.KZero.map_comp`: functoriality.
* `TauCeti.KZero.map_of_finiteProjectiveModulesRegular`: `[R] ↦ [S]`.
* `TauCeti.KZero.map_kZeroEquiv_of_mk`: `[eRⁿ] ↦ [f(e)Sⁿ]` for an idempotent matrix `e`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter II, §2.8 and
  Example 2.8.1, pp. 12–13, for the functoriality of `K₀` by extension of scalars.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2, for its description on
  idempotent matrices.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Matrix _root_.LinearMap _root_.Algebra

universe u

namespace KZero

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- **The homomorphism of `K₀` induced by a ring homomorphism** `f : R →+* S`. It sends the class
of a finitely generated projective right `R`-module `P` to the class of `P ⊗_R S`, the extension
of scalars of the left `Rᵐᵒᵖ`-module `P` along `fᵐᵒᵖ : Rᵐᵒᵖ →+* Sᵐᵒᵖ`
(`TauCeti.KZero.map_of_linearEquiv`). -/
def map (f : R →+* S) : KZero R →+ KZero S :=
  SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars

/-- `K₀(f)` sends the class of `P` to the class of its extension of scalars. -/
@[simp]
theorem map_of (f : R →+* S) (P : FiniteProjectiveRight R) :
    map f (SplitK0.of P) =
      SplitK0.of.{u} ((RingHom.op f).finiteProjectiveModulesExtendScalars.obj P) :=
  SplitK0.map_of.{u, u} _ P

/-- `K₀(f)` sends the class of `P` to the class of any finitely generated projective right
`S`-module isomorphic to `P ⊗_R S`, the balanced extension along `fᵐᵒᵖ`. -/
theorem map_of_linearEquiv (f : R →+* S) (P : FiniteProjectiveRight R)
    (Q : FiniteProjectiveRight S) (θ : BalancedExtension (RingHom.op f) P.obj ≃ₗ[Sᵐᵒᵖ] Q.obj) :
    map f (SplitK0.of P) = SplitK0.of.{u} Q :=
  (map_of f P).trans (SplitK0.of_extendScalars_obj θ)

variable (R) in
/-- Extension of scalars along the identity induces the identity on `K₀`. -/
@[simp]
theorem map_id : map (RingHom.id R) = AddMonoidHom.id (KZero R) :=
  SplitK0.hom_ext fun P ↦ map_of_linearEquiv _ P P
    ((BalancedExtension.congrRingHom (RingHom.ext fun _ ↦ rfl)).trans
      (BalancedExtension.lid Rᵐᵒᵖ P.obj))

/-- Extension of scalars along a composite `g ∘ f` induces the composite of the maps induced by
`f` and by `g`. -/
theorem map_comp (f : R →+* S) (g : S →+* T) : map (g.comp f) = (map g).comp (map f) := by
  -- Extending along `fᵐᵒᵖ` and then `gᵐᵒᵖ` agrees with extending along `(g ∘ f)ᵐᵒᵖ` and then
  -- along the identity, around the commuting square of opposite ring homomorphisms.
  have h : (map g).comp (map f) = (map (RingHom.id T)).comp (map (g.comp f)) :=
    (SplitK0.map_comp.{u, u, u} _ _).symm.trans <|
      (SplitK0.map_congr.{u, u} fun P ↦ ⟨(RingHom.finiteProjectiveModulesExtendScalarsCompIso
        (RingHom.op f) (RingHom.op g) (RingHom.op (g.comp f)) (RingHom.op (RingHom.id T))
        (RingHom.ext fun _ ↦ rfl)).app P⟩).trans (SplitK0.map_comp.{u, u, u} _ _)
  rw [h, map_id, AddMonoidHom.id_comp]

/-- Applying the maps induced by `f` and then by `g` is applying the map induced by `g ∘ f`. -/
@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : KZero R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, AddMonoidHom.comp_apply]

-- Not `@[simp]`: `simp` proves it from `TauCeti.KZero.map_of` and
-- `TauCeti.SplitK0.of_extendScalars_obj_finiteProjectiveModulesRegular`.
/-- `K₀(f)` sends the class `[R]` of the free right module of rank one to `[S]`. -/
theorem map_of_finiteProjectiveModulesRegular (f : R →+* S) :
    map f (SplitK0.of (finiteProjectiveModulesRegular Rᵐᵒᵖ)) =
      SplitK0.of.{u} (finiteProjectiveModulesRegular Sᵐᵒᵖ) :=
  (map_of f _).trans (SplitK0.of_extendScalars_obj_finiteProjectiveModulesRegular _)

/-- `TauCeti.KZero.map_kZeroEquiv_of_mk` for matrices indexed by `Fin n`, whose images are
modules in the universe of the rings. -/
private theorem map_kZeroEquiv_of_mk_fin {n : ℕ} (f : R →+* S) {e : Matrix (Fin n) (Fin n) R}
    (he : IsIdempotentElem e) :
    map f (IdempotentMonoid.kZeroEquiv R (GrothendieckAddGroup.of (IdempotentMonoid.mk e he))) =
      IdempotentMonoid.kZeroEquiv S
        (GrothendieckAddGroup.of (IdempotentMonoid.mk (e.map f) (he.matrix_map f))) := by
  -- Over the opposite ring, `eRⁿ` is the image of the row action of the transpose of `e`.
  have he' := he.matrix_transpose_map_op
  have hfe' := (he.matrix_map f).matrix_transpose_map_op
  let X : FiniteProjectiveRight R :=
    ⟨ModuleCat.of Rᵐᵒᵖ (range (eᵀ.map MulOpposite.op).vecMulLinear),
      finiteProjectiveModules_iff.2 ⟨inferInstance, he'.projective_range_vecMulLinear⟩⟩
  let Y : FiniteProjectiveRight S :=
    ⟨ModuleCat.of Sᵐᵒᵖ (range ((e.map f)ᵀ.map MulOpposite.op).vecMulLinear),
      finiteProjectiveModules_iff.2 ⟨inferInstance, hfe'.projective_range_vecMulLinear⟩⟩
  have hmap : (eᵀ.map MulOpposite.op).map (RingHom.op f) = (e.map f)ᵀ.map MulOpposite.op :=
    Matrix.ext fun _ _ ↦ rfl
  rw [IdempotentMonoid.kZeroEquiv_of_mk he X (rangeVecMulLinearTransposeMapOpEquiv e),
    IdempotentMonoid.kZeroEquiv_of_mk (he.matrix_map f) Y
      (rangeVecMulLinearTransposeMapOpEquiv (e.map f))]
  exact map_of_linearEquiv f X Y
    ((BalancedExtension.rangeVecMulLinearEquiv (RingHom.op f) he').trans
      (LinearEquiv.ofEq _ _ (by rw [hmap])))

-- Not `@[simp]`: the simp normal form of `Algebra.GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `Algebra.GrothendieckAddGroup.lift_apply_of`.
/-- **`K₀(f)` on idempotent matrices.** For an idempotent matrix `e` over `R`, `K₀(f)` sends the
class `[eRⁿ]` of the image of `e` acting on column vectors to the class `[f(e)Sⁿ]` of the image of
the matrix `f(e)`; in terms of the idempotent monoid, it applies `f` to the entries of `e`. -/
theorem map_kZeroEquiv_of_mk {ι : Type*} [Fintype ι] (f : R →+* S) {e : Matrix ι ι R}
    (he : IsIdempotentElem e) :
    map f (IdempotentMonoid.kZeroEquiv R (GrothendieckAddGroup.of (IdempotentMonoid.mk e he))) =
      IdempotentMonoid.kZeroEquiv S
        (GrothendieckAddGroup.of (IdempotentMonoid.mk (e.map f) (he.matrix_map f))) := by
  -- Relabel the indices by `Fin (card ι)`, which does not change the classes.
  let σ := (Fintype.equivFin ι).symm
  have h := idempotentEquivalent_submatrix he σ
  have hf := idempotentEquivalent_submatrix (he.matrix_map f) σ
  rw [IdempotentMonoid.mk_eq_mk h, IdempotentMonoid.mk_eq_mk hf,
    map_kZeroEquiv_of_mk_fin f h.isIdempotentElem_right]
  simp only [submatrix_map]

end KZero

end TauCeti
