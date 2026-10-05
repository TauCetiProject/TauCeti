/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.IdempotentCoordinate
public import TauCeti.CategoryTheory.Simple

/-!
# Simple classes in the graded Grothendieck group of finite graded modules

Let `A` be a finite-dimensional algebra over a field `k`, with homogeneous pieces
`𝒜 : ℤ → Submodule k A`. A finite graded `A`-module is finite-dimensional over `k`, so it has a
filtration by graded submodules whose successive quotients are simple objects of the graded
module category. If every simple finite graded module is an internal shift `Sᵢ{d}` of a member of
a family `S`, the relation `[M{d}] = qᵈ [M]` turns such a filtration into an expression of `[M]` as
a `ℤ[q,q⁻¹]`-linear combination of the classes `[Sᵢ]`. Thus these classes span the graded
Grothendieck group `G₀^gr(mod A)` over the Laurent ring.

This is the spanning half of the simple-class basis of `G₀^gr(mod A)`. Linear independence is
read off from the idempotent coordinates `TauCeti.gradedIdempotentCoordinate`: if degree-zero
idempotents `eᵢ` satisfy `gdim(eᵢ • Sⱼ) = δᵢⱼ`, as for the vertex idempotents and vertex simples of
a basic algebra whose simple modules are one-dimensional, the classes `[Sᵢ]` form a
`ℤ[q,q⁻¹]`-basis whose coordinates are the idempotent coordinates. This basis is the module-side
basis of the graded Cartan matrix `TauCeti.gradedCartanMatrix`.

## Main definitions

* `TauCeti.IsExhaustiveGradedSimpleFamily`: every simple finite graded module is isomorphic to an
  internal shift of a member of the family.
* `TauCeti.gradedSimpleClassBasis`: the `ℤ[q,q⁻¹]`-basis of `G₀^gr(mod A)` given by an
  exhaustive family with Kronecker-delta idempotent coordinates.

## Main results

* `TauCeti.span_range_laurentK0_of_eq_top`: the classes of an exhaustive family span
  `G₀^gr(mod A)` over `ℤ[q,q⁻¹]`.
* `TauCeti.gradedSimpleClassBasis_repr_apply`: the coordinates in the simple-class basis are the
  idempotent coordinates.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded modules
  and their degree shifts.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Grothendieck group as a `ℤ[q,q⁻¹]`-module.

The argument adapts the ungraded simple-class basis of
`TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis` (`TauCeti.simpleClassBasis`) to graded
modules and the Laurent-linear Grothendieck group.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe uk uA uI

/-! ### Exhaustive families of graded simples -/

section Exhaustive

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}

/-- A family of finite graded modules is an **exhaustive family of graded simples up to shift** if
every finite graded module which is a simple object of the graded module category is isomorphic to
an internal shift `(S i){d}` of a member of the family. -/
def IsExhaustiveGradedSimpleFamily (S : I → (gradedFiniteModules 𝒜).FullSubcategory) : Prop :=
  ∀ M : (gradedFiniteModules 𝒜).FullSubcategory, Simple M.obj →
    ∃ i d, Nonempty (M.obj ≅ (S i).obj.shiftObj d)

/-- Characterization of `IsExhaustiveGradedSimpleFamily`, for importing modules, to which the body
of the definition is not exposed. -/
theorem isExhaustiveGradedSimpleFamily_iff (S : I → (gradedFiniteModules 𝒜).FullSubcategory) :
    IsExhaustiveGradedSimpleFamily S ↔
      ∀ M : (gradedFiniteModules 𝒜).FullSubcategory, Simple M.obj →
        ∃ i d, Nonempty (M.obj ≅ (S i).obj.shiftObj d) :=
  Iff.rfl

end Exhaustive

/-! ### Spanning -/

section Span

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI} (S : I → (gradedFiniteModules 𝒜).FullSubcategory)

/-- A finite graded module which is neither zero nor simple has a nonzero proper graded submodule
`Y` with quotient `C`, so `[M] = [Y] + [C]` with both `Y` and `C` of smaller dimension. -/
private theorem exists_laurentK0_of_eq_add (M : (gradedFiniteModules 𝒜).FullSubcategory)
    [Nontrivial M.obj] (hs : ¬Simple M.obj) :
    ∃ Y C : (gradedFiniteModules 𝒜).FullSubcategory,
      Module.finrank k Y.obj < Module.finrank k M.obj ∧
        Module.finrank k C.obj < Module.finrank k M.obj ∧
          LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M =
            LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) Y +
              LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) C := by
  -- A nonzero module is a nonzero object, so it has a nonzero proper graded submodule.
  have hM : ¬IsZero M.obj := fun hM => by
    obtain ⟨x, hx⟩ := exists_ne (0 : M.obj)
    have hid : 𝟙 M.obj = 0 := hM.eq_of_src _ _
    exact hx (by simpa using LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom hid) x)
  obtain ⟨Y, f, hf, hf₀, hfiso⟩ := exists_mono_ne_zero_not_isIso_of_not_simple hM hs
  have hinj : Function.Injective f.hom := (GradedModuleCat.mono_iff_injective f).1 hf
  have hnsurj : ¬Function.Surjective f.hom := fun hsurj => hfiso <| by
    have := (GradedModuleCat.epi_iff_surjective f).2 hsurj
    exact isIso_of_mono_of_epi f
  have : Module.Finite k Y := FiniteDimensional.of_injective (f.hom.restrictScalars k) hinj
  have : Module.Finite A Y := Module.Finite.of_restrictScalars_finite k A Y
  let C := GradedModuleCat.cokernelObj f
  have : Module.Finite k C := Module.Finite.trans A C
  have : Nontrivial Y := by
    by_contra hY
    rw [not_nontrivial_iff_subsingleton] at hY
    exact hf₀ (GradedModuleCat.hom_ext (LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]))
  have : Nontrivial C := by
    by_contra hC
    rw [not_nontrivial_iff_subsingleton, Submodule.Quotient.subsingleton_iff,
      LinearMap.range_eq_top] at hC
    exact hnsurj hC
  -- Dimension is additive along `0 → Y → M → C → 0`.
  have hdim : Module.finrank k M.obj = Module.finrank k Y + Module.finrank k C := by
    let g : Y →ₗ[k] M.obj := f.hom.restrictScalars k
    let π : M.obj →ₗ[k] C := (GradedModuleCat.cokernelπ f).hom.restrictScalars k
    have hg : Function.Injective g := hinj
    have hπ : Function.Surjective π := (LinearMap.range f.hom).mkQ_surjective
    have hgπ : Function.Exact g π := LinearMap.exact_map_mkQ_range f.hom
    have h := Module.length_eq_add_of_exact g π hg hπ hgπ
    rw [Module.length_eq_finrank, Module.length_eq_finrank, Module.length_eq_finrank] at h
    exact_mod_cast h
  let T : ShortComplex (gradedFiniteModules 𝒜).FullSubcategory :=
    ShortComplex.mk (X₁ := ⟨Y, gradedFiniteModules_iff.2 inferInstance⟩)
      (X₃ := ⟨C, gradedFiniteModules_iff.2 inferInstance⟩)
      (ObjectProperty.homMk f) (ObjectProperty.homMk (GradedModuleCat.cokernelπ f))
      ((gradedFiniteModules 𝒜).ι.map_injective (by simp))
  have hT : (gradedFiniteModulesExactStructure 𝒜).Conflation T :=
    (gradedFiniteModulesExactStructure_conflation_iff T).2
      { exact := GradedModuleCat.exact_iff.2 (LinearMap.exact_map_mkQ_range f.hom)
        mono_f := hf
        epi_g := (GradedModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _) }
  refine ⟨T.X₁, T.X₃, ?_, ?_, LaurentK0.of_conflation.{uA} _ hT⟩
  · rw [hdim]
    exact Nat.lt_add_of_pos_right (Module.finrank_pos (R := k) (M := C))
  · rw [hdim]
    exact Nat.lt_add_of_pos_left (Module.finrank_pos (R := k) (M := Y))

private theorem laurentK0_of_mem_span (hS : IsExhaustiveGradedSimpleFamily S)
    (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M ∈
      Submodule.span (LaurentPolynomial ℤ)
        (Set.range fun i => LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i)) := by
  set G := Submodule.span (LaurentPolynomial ℤ)
    (Set.range fun i => LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i))
  -- Strong induction on the dimension of the underlying `k`-vector space.
  induction hn : Module.finrank k M.obj using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  -- A zero module has zero class.
  by_cases hn₀ : n = 0
  · have : Subsingleton M.obj := Module.finrank_zero_iff.mp (hn.trans hn₀)
    have hM : IsZero M := IsZero.of_full_of_faithful_of_isZero (gradedFiniteModules 𝒜).ι M
      ((IsZero.iff_id_eq_zero _).2
        (GradedModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim (α := M.obj) _ _)))
    rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hM, map_zero]
    exact G.zero_mem
  have : Nontrivial M.obj := Module.nontrivial_of_finrank_pos (by rw [hn]; omega)
  -- A simple module is a shift `Sᵢ{d}`, with class `qᵈ [Sᵢ]`.
  by_cases hs : Simple M.obj
  · obtain ⟨i, d, ⟨e⟩⟩ := hS M hs
    rw [LaurentK0.of_congr.{uA} _ (ObjectProperty.isoMk _ e :
        M ≅ ⟨(S i).obj.shiftObj d, gradedFiniteModules_shiftObj (S i).property d⟩),
      laurentK0_of_shiftObj]
    exact G.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  -- Otherwise the class splits into two classes of smaller dimension.
  obtain ⟨Y, C, hY, hC, h⟩ := exists_laurentK0_of_eq_add M hs
  rw [h]
  exact G.add_mem (ih _ (hn ▸ hY) Y rfl) (ih _ (hn ▸ hC) C rfl)

/-- **The classes of an exhaustive family of graded simples span `G₀^gr(mod A)` over
`ℤ[q,q⁻¹]`.** A finite graded module has a filtration by graded submodules with simple
subquotients, each of which is a shift `Sᵢ{d}` of a member of the family, with class
`qᵈ [Sᵢ]`. -/
theorem span_range_laurentK0_of_eq_top (hS : IsExhaustiveGradedSimpleFamily S) :
    Submodule.span (LaurentPolynomial ℤ)
        (Set.range fun i => LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i)) =
      ⊤ := by
  refine top_unique fun x _ => ?_
  clear ‹x ∈ ⊤›
  obtain ⟨x, rfl⟩ := (LaurentK0.ofExactK0.{uA} (gradedFiniteModulesExactStructure 𝒜)).surjective x
  induction x using ExactK0.induction_on with
  | zero => simp
  | of M => simpa using laurentK0_of_mem_span S hS M
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  | neg x hx => simpa using Submodule.neg_mem _ hx

end Span

/-! ### The simple-class basis -/

section Basis

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI} (S : I → (gradedFiniteModules 𝒜).FullSubcategory)
  {e : I → A} (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)

/-- **The simple-class basis of `G₀^gr(mod A)`** over `ℤ[q,q⁻¹]`. Its basis vector at `i` is the
class `[Sᵢ]`. The hypotheses say that the degree-zero idempotents `eᵢ` have graded dimensions
`gdim(eᵢ • Sⱼ) = δᵢⱼ`, and that every simple finite graded module is a shift of some `Sᵢ`. -/
def gradedSimpleClassBasis :
    Module.Basis I (LaurentPolynomial ℤ) (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :=
  Module.Basis.mk (linearIndependent_laurentK0_of_smulGradedDimension he he₀ S hne hself)
    (span_range_laurentK0_of_eq_top S hS).ge

/-- The basis vector indexed by `i` is the class `[Sᵢ]`. -/
@[simp]
theorem gradedSimpleClassBasis_apply (i : I) :
    gradedSimpleClassBasis S he he₀ hne hself hS i =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i) :=
  Module.Basis.mk_apply _ _ i

/-- The `i`th coordinate in the simple-class basis is the idempotent coordinate of `eᵢ`, the graded
dimension of `eᵢ • M` on the class of `M`. -/
@[simp]
theorem gradedSimpleClassBasis_repr_apply
    (x : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) (i : I) :
    (gradedSimpleClassBasis S he he₀ hne hself hS).repr x i =
      gradedIdempotentCoordinate (he i) (he₀ i) x := by
  classical
  refine LinearMap.congr_fun ((gradedSimpleClassBasis S he he₀ hne hself hS).ext
    (f₁ := (gradedSimpleClassBasis S he he₀ hne hself hS).coord i) fun j => ?_) x
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, gradedSimpleClassBasis_apply,
    gradedIdempotentCoordinate_of, Finsupp.single_apply]
  split_ifs with hji
  · subst hji
    exact (hself j).symm
  · exact (hne (Ne.symm hji)).symm

end Basis

end TauCeti
