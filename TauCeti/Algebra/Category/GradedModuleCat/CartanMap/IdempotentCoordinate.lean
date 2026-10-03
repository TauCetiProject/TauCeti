/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.GradedDimension

/-!
# Idempotent coordinates on the graded Grothendieck group of finite graded modules

Let `A` be a finite-dimensional algebra over a field `k`, with homogeneous pieces
`𝒜 : ℤ → Submodule k A`, and let `e ∈ 𝒜 0` be an idempotent of degree zero. For a finitely
generated graded `A`-module `M`, the subspaces `e • Mₚ` are finite-dimensional and vanish for all
but finitely many degrees `p`, so they have a graded dimension

```text
gdim_e(M) = ∑ₚ dim_k(e • Mₚ) qᵖ ∈ ℤ[q,q⁻¹].
```

Because `e` is an idempotent of degree zero, `M ↦ e • Mₚ` is exact in each degree, so `gdim_e` is
additive on short exact sequences of graded modules. Shifting the grading multiplies it by a power
of `q`, so it descends to a `ℤ[q,q⁻¹]`-linear coordinate

```text
TauCeti.gradedIdempotentCoordinate : G₀^gr(mod A) ⟶ ℤ[q,q⁻¹]
```

on the Laurent Grothendieck group of finite graded modules, the target of the graded Cartan map
`TauCeti.gradedCartanMap`.

For `e = 1` this is the graded dimension of `M`. In general `e • Mₚ` is the degree-`p` piece of
the summand `e • M`. Suppose the graded simple modules are the shifts `Sᵢ{d}` of modules `Sᵢ`
concentrated in degree zero, and the idempotents `eᵢ` satisfy `dim_k(eᵢ • Sⱼ) = δᵢⱼ`, as for the
vertex idempotents of a basic algebra whose simple modules are one-dimensional. Then additivity
along a graded composition series shows that `dim_k(eᵢ • Mₚ)` counts the composition factors of
`M` isomorphic to `Sᵢ{p}`, so these coordinates read graded composition multiplicities, and in
particular the entries of the graded Cartan matrix. The last result of this file turns
Kronecker-delta coordinates into linear independence of classes over `ℤ[q,q⁻¹]`.

## Main definitions

* `TauCeti.GradedModuleCat.smulPieceMap e f p`: the restriction `e • Mₚ ⟶ e • Nₚ` of a morphism of
  graded modules, where `e • Mₚ` is Mathlib's pointwise action on submodules.
* `TauCeti.GradedModuleCat.smulGradedDimension e M`: the graded dimension `∑ₚ dim_k(e • Mₚ) qᵖ`
  of a graded module that is finite-dimensional over `k`.
* `TauCeti.gradedIdempotentCoordinate`: the induced `ℤ[q,q⁻¹]`-linear coordinate on the graded
  Grothendieck group of finite graded modules.

## Main results

* `TauCeti.GradedModuleCat.exact_smulPieceMap`: for an idempotent `e` of degree zero, restriction
  to the subspaces `e • Mₚ` preserves exactness.
* `TauCeti.GradedModuleCat.smulGradedDimension_shortExact`: `gdim_e` is additive on short exact
  sequences of graded modules.
* `TauCeti.GradedModuleCat.smulGradedDimension_shiftObj`: `gdim_e(M{n}) = qⁿ gdim_e(M)`.
* `TauCeti.gradedIdempotentCoordinate_of`: the coordinate of the class of `M` is `gdim_e(M)`.
* `TauCeti.linearIndependent_laurentK0_of_smulGradedDimension`: classes with Kronecker-delta
  idempotent coordinates are linearly independent over `ℤ[q,q⁻¹]`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded modules
  and their degree shifts.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Grothendieck group as a `ℤ[q,q⁻¹]`-module and graded dimensions.
* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the ungraded coordinates `dim_k(e M)` on the
  Grothendieck group and the Cartan matrix.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial
open scoped Pointwise

universe v uk uA

namespace GradedModuleCat

/-! ### The subspaces `e • Mₚ` -/

section SMulPiece

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} (e : A) {M N P : GradedModuleCat.{v} 𝒜}

/-- A morphism of graded modules restricts to the subspaces `e • Mₚ ⟶ e • Nₚ`. -/
def smulPieceMap (f : M ⟶ N) (p : ℤ) :
    ↥(e • M.grading.piece p) →ₗ[k] ↥(e • N.grading.piece p) :=
  (f.hom.restrictScalars k).restrict fun x hx => by
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨f.hom y, map_mem f hy, (map_smul f.hom e y).symm⟩

@[simp]
theorem coe_smulPieceMap_apply (f : M ⟶ N) (p : ℤ) (x : ↥(e • M.grading.piece p)) :
    (smulPieceMap e f p x : N) = f.hom x :=
  (rfl)

@[simp]
theorem smulPieceMap_id (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    smulPieceMap e (𝟙 M) p = LinearMap.id :=
  (rfl)

@[simp]
theorem smulPieceMap_comp (f : M ⟶ N) (g : N ⟶ P) (p : ℤ) :
    smulPieceMap e (f ≫ g) p = smulPieceMap e g p ∘ₗ smulPieceMap e f p :=
  (rfl)

variable {e}

/-- Restriction to `e • Mₚ` preserves injectivity. -/
theorem smulPieceMap_injective {f : M ⟶ N} (hf : Function.Injective f.hom) (p : ℤ) :
    Function.Injective (smulPieceMap e f p) := fun _ _ hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))

/-- Restriction to `e • Mₚ` preserves surjectivity: a preimage can be chosen of degree `p`. -/
theorem smulPieceMap_surjective {g : N ⟶ P} (hg : Function.Surjective g.hom) (p : ℤ) :
    Function.Surjective (smulPieceMap e g p) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  obtain ⟨x, rfl⟩ := hg y
  -- The degree-`p` component of `x` maps to the degree-`p` component of `g x`, which is `g x`.
  have hxp : g.hom (DirectSum.decompose N.grading.piece x p : N) = g.hom x := by
    rw [g.isHomogeneous.map_decompose, add_zero, DirectSum.decompose_of_mem_same _ hy]
  refine ⟨⟨e • (DirectSum.decompose N.grading.piece x p : N),
    Submodule.smul_mem_pointwise_smul _ _ _ (DirectSum.decompose N.grading.piece x p).2⟩, ?_⟩
  ext
  simp [hxp]

/-- An element of degree zero carries `Mₚ` into itself. -/
theorem smul_grading_piece_le (he₀ : e ∈ 𝒜 0) (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    e • M.grading.piece p ≤ M.grading.piece p := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  simpa using SetLike.GradedSMul.smul_mem (B := M.grading.piece) he₀ hy

/-- **Restriction to `e • Mₚ` preserves exactness** when `e` is an idempotent of degree zero. -/
theorem exact_smulPieceMap (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0) {f : M ⟶ N} {g : N ⟶ P}
    (hfg : Function.Exact f.hom g.hom) (p : ℤ) :
    Function.Exact (smulPieceMap e f p) (smulPieceMap e g p) := by
  rintro ⟨z, hz⟩
  constructor
  · intro hgz
    obtain ⟨w, hw⟩ := (hfg z).1 (congrArg Subtype.val hgz)
    -- The degree-`p` component `w'` of `w` still maps to `z`, and then so does `e • w'`.
    let w' : M := DirectSum.decompose M.grading.piece w p
    have hw' : f.hom w' = z := by
      rw [f.isHomogeneous.map_decompose, add_zero, hw,
        DirectSum.decompose_of_mem_same _ (smul_grading_piece_le he₀ N p hz)]
    refine ⟨⟨e • w', Submodule.smul_mem_pointwise_smul _ _ _
      (DirectSum.decompose M.grading.piece w p).2⟩, ?_⟩
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    ext
    rw [coe_smulPieceMap_apply, map_smul, hw', smul_smul, he.eq]
  · rintro ⟨x, hx⟩
    rw [← hx]
    ext
    simp only [coe_smulPieceMap_apply, ZeroMemClass.coe_zero]
    exact (hfg _).2 ⟨_, rfl⟩

end SMulPiece

/-! ### The graded dimension of `e • M` -/

section SMulGradedDimension

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} (e : A) (M : GradedModuleCat.{v} 𝒜)

/-- A shift of a graded module has the same underlying `k`-module, so it is finite-dimensional
whenever the module is. -/
instance [Module.Finite k M] (n : ℤ) : Module.Finite k (M.shiftObj n) :=
  inferInstanceAs (Module.Finite k M)

/-- A graded module that is finite-dimensional over `k` has finitely many nonzero subspaces
`e • Mₚ`, all finite-dimensional. -/
theorem hasFiniteLaurentSupport_smul_grading_piece [Module.Finite k M] :
    HasFiniteLaurentSupport k fun p => ↥(e • M.grading.piece p) := by
  refine ⟨fun p => inferInstance, M.grading.finite_piece_ne_bot.subset fun p hp hbot => hp ?_⟩
  simp [hbot]

/-- The **graded dimension of `e • M`**, `∑ₚ dim_k(e • Mₚ) qᵖ`, for a graded module that is
finite-dimensional over `k`. -/
def smulGradedDimension [Module.Finite k M] : LaurentPolynomial ℤ :=
  gradedDimension k (fun p => ↥(e • M.grading.piece p))
    (M.hasFiniteLaurentSupport_smul_grading_piece e)

@[simp]
theorem coeff_smulGradedDimension [Module.Finite k M] (p : ℤ) :
    (M.smulGradedDimension e).coeff p = Module.finrank k ↥(e • M.grading.piece p) :=
  coeff_gradedDimension _ p

variable {M}

/-- Isomorphic graded modules have the same graded dimension of `e • M`. -/
theorem smulGradedDimension_congr {N : GradedModuleCat.{v} 𝒜} [Module.Finite k M]
    [Module.Finite k N] (i : M ≅ N) : M.smulGradedDimension e = N.smulGradedDimension e :=
  gradedDimension_congr _ _ fun p => LinearEquiv.finrank_eq <|
    LinearEquiv.ofLinearMap (smulPieceMap e i.hom p) (smulPieceMap e i.inv p)
      (by rw [← smulPieceMap_comp, i.inv_hom_id, smulPieceMap_id])
      (by rw [← smulPieceMap_comp, i.hom_inv_id, smulPieceMap_id])

variable (M)

/-- Shifting the grading multiplies the graded dimension of `e • M` by a power of `q`:
`gdim_e(M{n}) = qⁿ gdim_e(M)`. -/
@[simp]
theorem smulGradedDimension_shiftObj [Module.Finite k M] (n : ℤ) :
    (M.shiftObj n).smulGradedDimension e = T n * M.smulGradedDimension e := by
  have h := gradedDimension_reindex_add (M.hasFiniteLaurentSupport_smul_grading_piece e) (-n)
  rw [neg_neg] at h
  rw [smulGradedDimension, smulGradedDimension, ← h]
  exact gradedDimension_congr _ _ fun p => by rw [InternalGrading.shift_piece]

variable {M e}

/-- **The graded dimension of `e • M` is additive on short exact sequences** of graded modules
when `e` is an idempotent of degree zero. -/
theorem smulGradedDimension_shortExact (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0)
    {S : ShortComplex (GradedModuleCat.{v} 𝒜)} (hS : S.ShortExact) [Module.Finite k S.X₁]
    [Module.Finite k S.X₂] [Module.Finite k S.X₃] :
    S.X₂.smulGradedDimension e = S.X₁.smulGradedDimension e + S.X₃.smulGradedDimension e := by
  exact gradedDimension_shortExact _ _ _ _
    (fun p => smulPieceMap_injective ((mono_iff_injective S.f).1 hS.mono_f) p)
    (fun p => exact_smulPieceMap he he₀ (exact_iff.1 hS.exact) p)
    (fun p => smulPieceMap_surjective ((epi_iff_surjective S.g).1 hS.epi_g) p)

end SMulGradedDimension

end GradedModuleCat

/-! ### The coordinate on the graded Grothendieck group -/

section Coordinate

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [Module.Finite k A]

/-- Over a finite-dimensional algebra, a finitely generated graded module is finite-dimensional. -/
instance (M : (gradedFiniteModules 𝒜).FullSubcategory) : Module.Finite k M.obj :=
  Module.Finite.trans A M.obj

variable {e : A}

/-- The graded dimension of `e • M` as a shift-compatible invariant of finite graded modules. -/
private def smulGradedDimensionInvariant (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0) :
    GradedExactStructure.ShiftInvariant (gradedFiniteModulesExactStructure 𝒜)
      (laurentTAut ℤ (LaurentPolynomial ℤ)) where
  obj M := M.obj.smulGradedDimension e
  map_conflation S hS := by
    rw [gradedFiniteModulesExactStructure_conflation_iff] at hS
    have : Module.Finite k (S.map (gradedFiniteModules 𝒜).ι).X₁ :=
      inferInstanceAs (Module.Finite k S.X₁.obj)
    have : Module.Finite k (S.map (gradedFiniteModules 𝒜).ι).X₂ :=
      inferInstanceAs (Module.Finite k S.X₂.obj)
    have : Module.Finite k (S.map (gradedFiniteModules 𝒜).ι).X₃ :=
      inferInstanceAs (Module.Finite k S.X₃.obj)
    exact GradedModuleCat.smulGradedDimension_shortExact he he₀ hS
  map_shift M := by
    -- The restricted shift agrees with the ambient shift `M ↦ M{1}` up to isomorphism.
    have : Module.Finite k
        (((gradedFiniteModules 𝒜).ι ⋙ (GradedModuleCat.shift 𝒜).functor).obj M) :=
      inferInstanceAs (Module.Finite k M.obj)
    have : Module.Finite k
        (((gradedFiniteModulesExactStructure 𝒜).shift.functor ⋙
          (gradedFiniteModules 𝒜).ι).obj M) :=
      inferInstanceAs
        (Module.Finite k ((gradedFiniteModulesExactStructure 𝒜).shift.functor.obj M).obj)
    refine (GradedModuleCat.smulGradedDimension_congr e
      ((gradedFiniteModulesExactStructureShiftFunctorCompιIso (𝒜 := 𝒜)).app M)).trans ?_
    rw [laurentTAut_apply, smul_eq_mul]
    exact M.obj.smulGradedDimension_shiftObj e 1

/-- **The idempotent coordinate** on the graded Grothendieck group of finite graded modules over a
finite-dimensional algebra: the `ℤ[q,q⁻¹]`-linear map sending the class of `M` to the graded
dimension `∑ₚ dim_k(e • Mₚ) qᵖ` of `e • M`, for an idempotent `e` of degree zero. -/
def gradedIdempotentCoordinate (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0) :
    LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentPolynomial ℤ :=
  LaurentK0.lift _ (smulGradedDimensionInvariant he he₀)

/-- **The idempotent coordinate of a class.** Evaluating `gradedIdempotentCoordinate` on the class
`[M]` of a finite graded module recovers the graded dimension `∑ₚ dim_k(e • Mₚ) qᵖ` of `e • M`. -/
@[simp]
theorem gradedIdempotentCoordinate_of (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0)
    (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    gradedIdempotentCoordinate he he₀
        (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M) =
      M.obj.smulGradedDimension e :=
  LaurentK0.lift_of.{uA} _ M

/-- **Classes with Kronecker-delta idempotent coordinates are linearly independent.** If the
graded dimension of `eᵢ • Sⱼ` is `1` for `i = j` and `0` otherwise, the classes of the finite
graded modules `Sⱼ` are linearly independent over `ℤ[q,q⁻¹]`. -/
theorem linearIndependent_laurentK0_of_smulGradedDimension {I : Type*} {e : I → A}
    (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1) :
    LinearIndependent (LaurentPolynomial ℤ) fun i =>
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i) :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun i => gradedIdempotentCoordinate (he i) (he₀ i))
    (fun i j hij => by simpa using hne hij) (fun i => by simpa using hself i)

end Coordinate

end TauCeti
