/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic

/-!
# Derived fixed points of an endomorphism

An algebra for the identity endofunctor on cochain complexes is a complex `M` with an
endomorphism `φ`. Its derived fixed points are the mapping cocone of `φ - 1`, viewed in
the derived category. For a semilinear Frobenius, this construction is applied after
restriction to a ring of Frobenius-fixed scalars; subtraction of the identity is linear
over those scalars, but generally not over the original coefficient ring.

The construction is functorial in strictly commuting maps. Its distinguished triangle
gives the long exact cohomology sequence and bounds its amplitude. In particular a
complex concentrated in degree zero can have fixed-point cohomology in degree one.
No enhancement or category of homotopy-coherent endomorphisms is constructed here.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, §9, Lemma 9.2.
* B. Bhatt and J. Lurie, *Absolute prismatic cohomology*, Example 8.1.3.
-/

public section

noncomputable section

universe w v u

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Endofunctor.Algebra

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

/-- The natural endomorphism `φ - 1` of the forgetful functor on complexes with an
endomorphism. This is formed in the category of the fixed scalars. -/
@[expose]
def fixedPointsDifference :
    forget (𝟭 (CochainComplex C ℤ)) ⟶ forget (𝟭 (CochainComplex C ℤ)) where
  -- `id` fixes the arrow type before subtraction: `str` is natively typed from
  -- the identity functor's value, which elaboration need not reduce at this point.
  app M := id (α := M.a ⟶ M.a) M.str - 𝟙 M.a
  naturality M N f := by
    -- Re-elaborate at the carrier: the native forgetful functor and identity functor
    -- have definitionally equal carriers which are not reduced by `simp`'s transparency.
    change f.f ≫ (id (α := N.a ⟶ N.a) N.str - 𝟙 N.a) =
      (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) ≫ f.f
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp]
    exact congrArg (· - f.f) f.h

variable [HasBinaryBiproducts C]

/-- The cochain model for derived fixed points: the mapping cone of `φ - 1`, shifted
by `-1`. Morphisms are induced by the same equivariant map on both cone terms. -/
@[expose, implicit_reducible]
def fixedPointsComplexFunctor :
    Algebra (𝟭 (CochainComplex C ℤ)) ⥤ CochainComplex C ℤ :=
  NatTrans.mappingCoconeFunctor fixedPointsDifference

/-- The cochain model of the derived fixed points of an endomorphism. -/
abbrev fixedPointsComplex (M : Algebra (𝟭 (CochainComplex C ℤ))) : CochainComplex C ℤ :=
  fixedPointsComplexFunctor.obj M

/-- The canonical projection from the fixed-point complex to the original complex. -/
@[implicit_reducible]
def fixedPointsComplexι :
    fixedPointsComplexFunctor (C := C) ⟶ forget (𝟭 (CochainComplex C ℤ)) :=
  NatTrans.mappingCoconeFunctorFst fixedPointsDifference

@[simp]
lemma fixedPointsComplex_eq (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsComplex =
      CochainComplex.mappingCocone (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) := (rfl)

@[simp]
lemma fixedPointsComplexι_app (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    fixedPointsComplexι.app M =
      CochainComplex.mappingCocone.fst (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) := (rfl)

end Preadditive

variable [Abelian C] [HasDerivedCategory.{w} C]

/-- Derived fixed points as a functor to the derived category of the fixed scalars. -/
@[expose, implicit_reducible]
def fixedPointsFunctor :
    Algebra (𝟭 (CochainComplex C ℤ)) ⥤ DerivedCategory C :=
  fixedPointsComplexFunctor ⋙ DerivedCategory.Q

/-- The derived fixed points `fib(φ - 1)`. -/
abbrev fixedPoints (M : Algebra (𝟭 (CochainComplex C ℤ))) : DerivedCategory C :=
  fixedPointsFunctor.obj M

/-- The projection from derived fixed points to the original complex. -/
@[implicit_reducible]
def fixedPointsι (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPoints ⟶ DerivedCategory.Q.obj M.a :=
  DerivedCategory.Q.map (fixedPointsComplexι.app M)

/-- The fixed-point fibre triangle, with second map `φ - 1`. -/
@[expose, implicit_reducible]
def fixedPointsTriangle (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    Triangle (DerivedCategory C) :=
  DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a))

@[simp]
lemma fixedPointsTriangle_obj₁ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.obj₁ = M.fixedPoints := (rfl)

@[simp]
lemma fixedPointsTriangle_obj₂ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.obj₂ = DerivedCategory.Q.obj M.a := (rfl)

@[simp]
lemma fixedPointsTriangle_obj₃ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.obj₃ = DerivedCategory.Q.obj M.a := (rfl)

@[simp]
lemma fixedPointsTriangle_mor₁ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.mor₁ = M.fixedPointsι := (rfl)

@[simp]
lemma fixedPointsTriangle_mor₂ (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle.mor₂ = DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str) - 𝟙 _ := by
  simp [fixedPointsTriangle]

/-- The fixed-point fibre triangle is distinguished. -/
theorem fixedPointsTriangle_distinguished (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsTriangle ∈ distTriang (DerivedCategory C) :=
  DerivedCategory.mappingCocone_triangle_distinguished _

@[reassoc]
lemma fixedPointsι_comp (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    M.fixedPointsι ≫ (DerivedCategory.Q.map (id (α := M.a ⟶ M.a) M.str) - 𝟙 _) = 0 := by
  rw [← fixedPointsTriangle_mor₂]
  exact comp_distTriang_mor_zero₁₂ _ M.fixedPointsTriangle_distinguished

@[reassoc]
lemma fixedPointsι_naturality {M N : Algebra (𝟭 (CochainComplex C ℤ))} (f : M ⟶ N) :
    fixedPointsFunctor.map f ≫ N.fixedPointsι = M.fixedPointsι ≫ DerivedCategory.Q.map f.f := by
  exact (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg (DerivedCategory.Q.map) (fixedPointsComplexι.naturality f)).trans
      (DerivedCategory.Q.map_comp _ _))

/-- An equivariant quasi-isomorphism induces an isomorphism on derived fixed points. -/
instance isIso_fixedPointsFunctor_map {M N : Algebra (𝟭 (CochainComplex C ℤ))}
    (f : M ⟶ N) [QuasiIso f.f] : IsIso (fixedPointsFunctor.map f) := by
  let φ := fixedPointsDifference.app M
  let ψ := fixedPointsDifference.app N
  have h : φ ≫ f.f = f.f ≫ ψ := (fixedPointsDifference.naturality f).symm
  have hcone : QuasiIso (CochainComplex.mappingCone.map φ ψ f.f f.f h) := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map
        (CochainComplex.mappingCone.triangleMap φ ψ f.f f.f h))
      (DerivedCategory.mappingCone_triangle_distinguished φ)
      (DerivedCategory.mappingCone_triangle_distinguished ψ)
      (inferInstanceAs (IsIso (DerivedCategory.Q.map f.f)))
      (inferInstanceAs (IsIso (DerivedCategory.Q.map f.f)))
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    ((CochainComplex.mappingCone.map φ ψ f.f f.f h)⟦(-1 : ℤ)⟧')))

/-- Derived fixed points vanish precisely when `φ - 1` is a quasi-isomorphism. -/
theorem isZero_fixedPoints_iff (M : Algebra (𝟭 (CochainComplex C ℤ))) :
    IsZero M.fixedPoints ↔ QuasiIso (id (α := M.a ⟶ M.a) M.str - 𝟙 M.a) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact M.fixedPointsTriangle.isZero₁_iff_isIso₂ M.fixedPointsTriangle_distinguished

section Cohomology

open DerivedCategory

variable (M : Algebra (𝟭 (CochainComplex C ℤ))) (n : ℤ)

/-- The boundary map `H^(n-1)(M) → H^n(M^(φ=1))`. -/
def fixedPointsδ :
    (homologyFunctor C (n - 1)).obj (Q.obj M.a) ⟶
      (homologyFunctor C n).obj M.fixedPoints :=
  HomologySequence.δ M.fixedPointsTriangle (n - 1) n (by omega)

@[reassoc (attr := simp)]
lemma fixedPointsδ_comp :
    M.fixedPointsδ n ≫ (homologyFunctor C n).map M.fixedPointsι = 0 :=
  HomologySequence.δ_comp _ M.fixedPointsTriangle_distinguished _ _ _

@[reassoc]
lemma comp_fixedPointsδ :
    (homologyFunctor C (n - 1)).map M.fixedPointsTriangle.mor₂ ≫ M.fixedPointsδ n = 0 :=
  HomologySequence.comp_δ _ M.fixedPointsTriangle_distinguished _ _ _

/-- The map from the cokernel of `φ - 1` on `H^(n-1)(M)` to fixed-point cohomology. -/
def fixedPointsCohomologyι :
    cokernel ((homologyFunctor C (n - 1)).map M.fixedPointsTriangle.mor₂) ⟶
      (homologyFunctor C n).obj M.fixedPoints :=
  cokernel.desc _ (M.fixedPointsδ n) (M.comp_fixedPointsδ n)

/-- The projection of fixed-point cohomology to the kernel of `φ - 1` on `H^n(M)`. -/
def fixedPointsCohomologyπ :
    (homologyFunctor C n).obj M.fixedPoints ⟶
      kernel ((homologyFunctor C n).map M.fixedPointsTriangle.mor₂) :=
  kernel.lift _ ((homologyFunctor C n).map M.fixedPointsι) (by
    exact (homologyFunctor C 0).homologySequence_comp
      M.fixedPointsTriangle M.fixedPointsTriangle_distinguished n)

@[reassoc (attr := simp)]
lemma cokernel_π_fixedPointsCohomologyι :
    cokernel.π ((homologyFunctor C (n - 1)).map M.fixedPointsTriangle.mor₂) ≫
      M.fixedPointsCohomologyι n = M.fixedPointsδ n :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma fixedPointsCohomologyπ_kernel_ι :
    M.fixedPointsCohomologyπ n ≫
      kernel.ι ((homologyFunctor C n).map M.fixedPointsTriangle.mor₂) =
        (homologyFunctor C n).map M.fixedPointsι :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
lemma fixedPointsCohomologyι_π :
    M.fixedPointsCohomologyι n ≫ M.fixedPointsCohomologyπ n = 0 := by
  rw [← cancel_epi (cokernel.π _), ← cancel_mono (kernel.ι _)]
  simp

/-- The canonical sequence
`coker(φ - 1 on H^(n-1)(M)) → H^n(M^(φ=1)) → ker(φ - 1 on H^n(M))`. -/
@[simps, implicit_reducible]
def fixedPointsCohomologySequence : ShortComplex C :=
  ShortComplex.mk (M.fixedPointsCohomologyι n) (M.fixedPointsCohomologyπ n)
    (M.fixedPointsCohomologyι_π n)

/-- The cokernel term embeds into fixed-point cohomology. -/
instance mono_fixedPointsCohomologyι : Mono (M.fixedPointsCohomologyι n) :=
  (HomologySequence.exact₃ _ M.fixedPointsTriangle_distinguished (n - 1) n
    (by omega)).mono_cokernelDesc

/-- Fixed-point cohomology surjects onto the kernel term. -/
instance epi_fixedPointsCohomologyπ : Epi (M.fixedPointsCohomologyπ n) :=
  (HomologySequence.exact₂ _ M.fixedPointsTriangle_distinguished n).epi_kernelLift

/-- The canonical kernel/cokernel sequence for derived fixed points is short exact. -/
theorem fixedPointsCohomologySequence_shortExact :
    (M.fixedPointsCohomologySequence n).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_
    (mono_fixedPointsCohomologyι M n) (epi_fixedPointsCohomologyπ M n)
  let S := ShortComplex.mk (M.fixedPointsδ n) ((homologyFunctor C n).map M.fixedPointsι)
    (M.fixedPointsδ_comp n)
  have hS : S.Exact := HomologySequence.exact₁ _ M.fixedPointsTriangle_distinguished
    (n - 1) n (by omega)
  let U := ShortComplex.mk (M.fixedPointsδ n) (M.fixedPointsCohomologyπ n) (by
    rw [← cancel_mono (kernel.ι _)]
    simp)
  let f : U ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι _
      comm₁₂ := by simp [S, U]
      comm₂₃ := by simp [S, U] }
  have hU : U.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mpr hS
  let g : U ⟶ M.fixedPointsCohomologySequence n :=
    { τ₁ := cokernel.π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [U, fixedPointsCohomologySequence]
      comm₂₃ := by simp [U, fixedPointsCohomologySequence] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono g).mp hU

/-- If the preceding cohomology vanishes, fixed-point cohomology is the kernel of
`φ - 1` in the current degree. The isomorphism is the canonical projection. -/
def fixedPointsCohomologyIsoKernel
    (h : IsZero ((homologyFunctor C (n - 1)).obj (Q.obj M.a))) :
    (homologyFunctor C n).obj M.fixedPoints ≅
      kernel ((homologyFunctor C n).map M.fixedPointsTriangle.mor₂) := by
  have hz : IsZero (cokernel
      ((homologyFunctor C (n - 1)).map M.fixedPointsTriangle.mor₂)) :=
    h.of_epi (cokernel.π _)
  have : IsIso (M.fixedPointsCohomologyπ n) :=
    (M.fixedPointsCohomologySequence_shortExact n).isIso_g_iff.mpr hz
  exact asIso (M.fixedPointsCohomologyπ n)

@[simp]
lemma fixedPointsCohomologyIsoKernel_hom
    (h : IsZero ((homologyFunctor C (n - 1)).obj (Q.obj M.a))) :
    (M.fixedPointsCohomologyIsoKernel n h).hom = M.fixedPointsCohomologyπ n := (rfl)

/-- If the current cohomology vanishes, fixed-point cohomology is the cokernel of
`φ - 1` in the preceding degree. Its inverse is the canonical boundary map. -/
def fixedPointsCohomologyIsoCokernel
    (h : IsZero ((homologyFunctor C n).obj (Q.obj M.a))) :
    (homologyFunctor C n).obj M.fixedPoints ≅
      cokernel ((homologyFunctor C (n - 1)).map M.fixedPointsTriangle.mor₂) := by
  have hz : IsZero (kernel ((homologyFunctor C n).map M.fixedPointsTriangle.mor₂)) :=
    h.of_mono (kernel.ι _)
  have : IsIso (M.fixedPointsCohomologyι n) :=
    (M.fixedPointsCohomologySequence_shortExact n).isIso_f_iff.mpr hz
  exact (asIso (M.fixedPointsCohomologyι n)).symm

@[simp]
lemma fixedPointsCohomologyIsoCokernel_inv
    (h : IsZero ((homologyFunctor C n).obj (Q.obj M.a))) :
    (M.fixedPointsCohomologyIsoCokernel n h).inv = M.fixedPointsCohomologyι n := (rfl)

/-- Derived fixed points preserve a lower cohomological bound. -/
theorem fixedPoints_isGE (a : ℤ) [(Q.obj M.a).IsGE a] : M.fixedPoints.IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (HomologySequence.exact₁ _ M.fixedPointsTriangle_distinguished
    (i - 1) i (by omega)).isZero_of_both_zeros
      ((DerivedCategory.isZero_of_isGE (Q.obj M.a) a (i - 1) (by omega)).eq_of_src _ _)
      ((DerivedCategory.isZero_of_isGE (Q.obj M.a) a i hi).eq_of_tgt _ _)

/-- Derived fixed points increase an upper cohomological bound by at most one. -/
theorem fixedPoints_isLE (b : ℤ) [(Q.obj M.a).IsLE b] : M.fixedPoints.IsLE (b + 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (HomologySequence.exact₁ _ M.fixedPointsTriangle_distinguished
    (i - 1) i (by omega)).isZero_of_both_zeros
      ((DerivedCategory.isZero_of_isLE (Q.obj M.a) b (i - 1) (by omega)).eq_of_src _ _)
      ((DerivedCategory.isZero_of_isLE (Q.obj M.a) b i (by omega)).eq_of_tgt _ _)

end Cohomology

/-! The identity on an object in degree zero has that object as its degree-one
fixed-point cohomology. In particular this applies to a nonzero `𝔽_p`-module. -/

example (X : C) :
    let M : Algebra (𝟭 (CochainComplex C ℤ)) :=
      ⟨(CochainComplex.singleFunctor C 0).obj X, 𝟙 _⟩
    (DerivedCategory.homologyFunctor C 1).obj M.fixedPoints ≅ X := by
  intro M
  have hz : IsZero ((DerivedCategory.homologyFunctor C 1).obj
      (DerivedCategory.Q.obj M.a)) :=
    DerivedCategory.isZero_of_isLE _ 0 1 (by omega)
  have hφ : (DerivedCategory.homologyFunctor C 0).map M.fixedPointsTriangle.mor₂ = 0 := by
    simp [M]
  exact M.fixedPointsCohomologyIsoCokernel 1 hz ≪≫
    cokernelIsoOfEq hφ ≪≫ cokernelZeroIsoTarget ≪≫
    (DerivedCategory.homologyFunctorFactors C 0).app M.a ≪≫
    (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) 0).app X

/-! Zero Frobenius has no derived fixed points, even on an unbounded complex. -/

example (K : CochainComplex C ℤ) :
    IsZero (fixedPoints (⟨K, 0⟩ : Algebra (𝟭 (CochainComplex C ℤ)))) := by
  rw [isZero_fixedPoints_iff]
  simp only [id_eq, zero_sub]
  have : IsIso (-𝟙 K) := inferInstanceAs (IsIso (-Iso.refl K).hom)
  infer_instance

end CategoryTheory.Endofunctor.Algebra
