/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import TauCeti.CategoryTheory.Sites.CommRingCat
public import TauCeti.CategoryTheory.Sites.Continuous

/-!
# The structure sheaf of the big fpqc site and the sheaves `𝔾_a`, `𝔾_m`, `μ_n`

For a scheme `S`, the big fpqc site over `S` is the category `Over S` of `S`-schemes with the
topology `Scheme.fpqcTopology.over S`. This file constructs its structure sheaf
`T ↦ Γ(T, O_T)` and the three basic sheaves of abelian groups built from it:

* the additive group `𝔾_a : T ↦ Γ(T, O_T)`;
* the multiplicative group `𝔾_m : T ↦ Γ(T, O_T)ˣ`, written additively;
* the sheaf of `n`-th roots of unity `μ_n : T ↦ {t ∈ Γ(T, O_T)ˣ | tⁿ = 1}`, for every `n`.

The sheaf property of `T ↦ Γ(T, O_T)` comes from representability: ring maps `R ⟶ Γ(T, O_T)`
are morphisms `T ⟶ Spec R`, so for every subcanonical topology on schemes, in particular the
fpqc topology, the global sections functor is a sheaf of commutative rings. The sheaves `𝔾_a`
and `𝔾_m` are obtained by composing with limit-preserving functors, and `μ_n` is the kernel of
the `n`-th power map `𝔾_m ⟶ 𝔾_m` (`isLimitMuKernelFork`). The sheaf `μ_n` is defined for
every `n`, not only for `n` invertible on `S`. For every topology `J` on schemes coarser than the
fpqc topology, `μ_n`, regarded as a sheaf for `J`, is still the kernel of the `n`-th power map
(`isLimitMuKernelForkMap`), because regarding an fpqc sheaf as a `J`-sheaf preserves finite limits.

## Main declarations

* `CategoryTheory.GrothendieckTopology.isSheaf_Γ`: `Γ` is a sheaf for every subcanonical topology.
* `AlgebraicGeometry.Scheme.bigStructureSheaf`: the sheaf of commutative rings `T ↦ Γ(T, O_T)`
  on the big fpqc site over `S`, and `AlgebraicGeometry.Scheme.bigRingCatSheaf`, the same sheaf
  as a sheaf of rings, over which sheaves of modules on the big site are defined.
* `AlgebraicGeometry.Scheme.Ga`, `AlgebraicGeometry.Scheme.Gm`, `AlgebraicGeometry.Scheme.mu`:
  the sheaves `𝔾_a`, `𝔾_m` and `μ_n`.
* `AlgebraicGeometry.Scheme.gaObjSpecEquiv`, `AlgebraicGeometry.Scheme.gmObjSpecEquiv`,
  `AlgebraicGeometry.Scheme.muObjSpecEquiv`: the values `R`, `Rˣ` and `μ_n(R)` of `𝔾_a`, `𝔾_m`
  and `μ_n` on an affine `S`-scheme `Spec R`.
* `AlgebraicGeometry.Scheme.powHom`: the `n`-th power map of `𝔾_m`.
* `AlgebraicGeometry.Scheme.isLimitMuKernelFork`: `μ_n` is the kernel of `powHom`.
* `AlgebraicGeometry.Scheme.isLimitMuKernelForkMap`: the same holds for every topology coarser
  than the fpqc topology, such as the étale topology.

## References

* [Stacks Project, Section 59.28 (03PK)](https://stacks.math.columbia.edu/tag/03PK)
-/

public section

open CategoryTheory Limits Opposite

universe u

open AlgebraicGeometry

/-- Ring maps `R ⟶ Γ(T, ⊤)` correspond naturally in `T` to morphisms `T ⟶ Spec R`: the global
sections functor composed with `Hom(R, -)` is represented by `Spec R`. -/
noncomputable def CommRingCat.ΓCompCoyonedaIso (R : CommRingCat.{u}) :
    Scheme.Γ ⋙ CategoryTheory.coyoneda.obj (op R) ≅ yoneda.obj (Spec R) :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso <| (opEquiv _ _).symm.trans <| ΓSpec.adjunction.homEquiv T.unop (op R))
    (fun f ↦ by
      ext φ
      exact ΓSpec.adjunction.homEquiv_naturality_left f.unop φ.op)

/-- The global sections functor `T ↦ Γ(T, ⊤)` is a sheaf of commutative rings for every
subcanonical topology on schemes. -/
theorem CategoryTheory.GrothendieckTopology.isSheaf_Γ (J : GrothendieckTopology Scheme.{u})
    [J.Subcanonical] : Presheaf.IsSheaf J Scheme.Γ := fun R ↦
  Presieve.isSheaf_iso J R.ΓCompCoyonedaIso.symm
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The structure sheaf `T ↦ Γ(T, O_T)` of the big fpqc site over `S`, as a sheaf of commutative
rings. It is the restriction to `Over S` of the global sections sheaf on all schemes. -/
@[expose]
noncomputable def bigStructureSheaf : Sheaf (fpqcTopology.over S) CommRingCat.{u} :=
  (fpqcTopology.overPullback CommRingCat.{u} S).obj ⟨Scheme.Γ, fpqcTopology.isSheaf_Γ⟩

@[simp]
lemma bigStructureSheaf_obj (T : Over S) :
    (bigStructureSheaf S).obj.obj (op T) = Γ(T.left, ⊤) := rfl

@[simp]
lemma bigStructureSheaf_map {T T' : Over S} (f : T ⟶ T') :
    (bigStructureSheaf S).obj.map f.op = f.left.appTop := rfl

/-- The structure sheaf `T ↦ Γ(T, O_T)` of the big fpqc site over `S`, as a sheaf of rings. This is
the ring over which sheaves of modules on the big site are defined. -/
@[expose]
noncomputable def bigRingCatSheaf : Sheaf (fpqcTopology.over S) RingCat.{u} :=
  (sheafCompose (fpqcTopology.over S) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (bigStructureSheaf S)

lemma bigRingCatSheaf_obj (T : Over S) :
    (bigRingCatSheaf S).obj.obj (op T) = (forget₂ CommRingCat RingCat).obj Γ(T.left, ⊤) :=
  rfl

lemma bigRingCatSheaf_map {T T' : Over S} (f : T ⟶ T') :
    (bigRingCatSheaf S).obj.map f.op = (forget₂ CommRingCat RingCat).map f.left.appTop :=
  rfl

/-- The value of the big structure sheaf on an affine `S`-scheme `Spec R` is the ring `R`. -/
noncomputable def bigStructureSheafObjSpecIso (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (bigStructureSheaf S).obj.obj (op (Over.mk h)) ≅ R :=
  Scheme.ΓSpecIso R

/-- The additive group `𝔾_a : T ↦ Γ(T, O_T)` on the big fpqc site over `S`: the underlying
sheaf of abelian groups of the big structure sheaf. -/
@[expose]
noncomputable def Ga : Sheaf (fpqcTopology.over S) AddCommGrpCat.{u} where
  obj := (bigStructureSheaf S).obj ⋙ forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat
  property := by
    -- Pin the limit size `{u, u + 1}` of the site; elaborating the instance inline unifies it
    -- with `PreservesLimits` at the wrong universe.
    have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget CommMonCat.{u}) :=
      inferInstance
    exact Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u}) <|
      Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget CommMonCat.{u}) <|
      Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat.{u} CommMonCat.{u})
        (bigStructureSheaf S).property

lemma Ga_obj (T : Over S) :
    (Ga S).obj.obj (op T) = AddCommGrpCat.of Γ(T.left, ⊤) := rfl

@[simp]
lemma Ga_map_apply {T T' : Over S} (f : T ⟶ T') (a : Γ(T'.left, ⊤)) :
    (Ga S).obj.map f.op a = f.left.appTop a := rfl

/-- The value of `𝔾_a` on an affine `S`-scheme `Spec R` is the additive group of `R`. -/
noncomputable def gaObjSpecEquiv (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (Ga S).obj.obj (op (Over.mk h)) ≃+ R :=
  -- By `Ga_obj` (`rfl`), the value of `𝔾_a` is the additive group of the big structure sheaf.
  (bigStructureSheafObjSpecIso S R h).commRingCatIsoToRingEquiv.toAddEquiv

@[simp]
lemma gaObjSpecEquiv_apply (R : CommRingCat.{u}) (h : Spec R ⟶ S) (a : Γ(Spec R, ⊤)) :
    gaObjSpecEquiv S R h a = (Scheme.ΓSpecIso R).hom a := (rfl)

@[simp]
lemma gaObjSpecEquiv_symm_apply (R : CommRingCat.{u}) (h : Spec R ⟶ S) (r : R) :
    (gaObjSpecEquiv S R h).symm r = (Scheme.ΓSpecIso R).inv r := (rfl)

/-- The multiplicative group `𝔾_m : T ↦ Γ(T, O_T)ˣ` on the big fpqc site over `S`, written
additively so that it is a sheaf of abelian groups. -/
@[expose]
noncomputable def Gm : Sheaf (fpqcTopology.over S) AddCommGrpCat.{u} where
  obj := (bigStructureSheaf S).obj ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    CommGrpCat.toAddCommGrp
  property := by
    -- As for `Ga`, pin the limit size `{u, u + 1}` of the site.
    have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget CommGrpCat.{u}) :=
      inferInstance
    exact Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u}) <|
      Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget CommGrpCat.{u}) <|
      Presheaf.isSheaf_comp_of_isSheaf _ _ CommMonCat.units.{u} <|
      Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat.{u} CommMonCat.{u})
        (bigStructureSheaf S).property

lemma Gm_obj (T : Over S) :
    (Gm S).obj.obj (op T) = AddCommGrpCat.of (Additive Γ(T.left, ⊤)ˣ) := rfl

@[simp]
lemma Gm_map_apply {T T' : Over S} (f : T ⟶ T') (u : Additive Γ(T'.left, ⊤)ˣ) :
    (Gm S).obj.map f.op u = Additive.ofMul (Units.map f.left.appTop.hom.toMonoidHom u.toMul) := rfl

/-- The value of `𝔾_m` on an affine `S`-scheme `Spec R` is the unit group of `R`, written
additively. -/
noncomputable def gmObjSpecEquiv (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (Gm S).obj.obj (op (Over.mk h)) ≃+ Additive Rˣ :=
  -- By `Gm_obj` (`rfl`), the value of `𝔾_m` on `Spec R` is `Additive Γ(Spec R, ⊤)ˣ`.
  (MulEquiv.toAdditive (Units.mapEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv) :
    Additive Γ(Spec R, ⊤)ˣ ≃+ Additive Rˣ)

@[simp]
lemma coe_gmObjSpecEquiv_apply (R : CommRingCat.{u}) (h : Spec R ⟶ S)
    (u : Additive Γ(Spec R, ⊤)ˣ) :
    ((gmObjSpecEquiv S R h u).toMul : R) = (Scheme.ΓSpecIso R).hom (u.toMul : Γ(Spec R, ⊤)) :=
  (rfl)

@[simp]
lemma coe_gmObjSpecEquiv_symm_apply (R : CommRingCat.{u}) (h : Spec R ⟶ S) (u : Additive Rˣ) :
    (Additive.toMul (α := Γ(Spec R, ⊤)ˣ) ((gmObjSpecEquiv S R h).symm u) :
      Γ(Spec R, ⊤)) = (Scheme.ΓSpecIso R).inv (u.toMul : R) :=
  (rfl)

/-- The `n`-th power map `𝔾_m ⟶ 𝔾_m`, `t ↦ tⁿ`. In the additive notation of `Gm` it is
multiplication by `n`. -/
noncomputable def powHom (n : ℕ) : Gm S ⟶ Gm S where
  hom :=
    { app T := AddCommGrpCat.ofHom (powMonoidHom n).toAdditive
      naturality T T' f := by
        ext u
        exact (map_pow (Units.map f.unop.left.appTop.hom.toMonoidHom)
          (Additive.toMul (α := Γ(T.unop.left, ⊤)ˣ) u) n).symm }

@[simp]
lemma powHom_app_apply (n : ℕ) (T : Over S) (u : Additive Γ(T.left, ⊤)ˣ) :
    (powHom S n).hom.app (op T) u = Additive.ofMul (u.toMul ^ n) := (rfl)

/-- On an affine test scheme `Spec R`, the `n`-th power map of `𝔾_m` is `u ↦ uⁿ` on `Rˣ`,
which is multiplication by `n` in additive notation. -/
lemma gmObjSpecEquiv_powHom_app (n : ℕ) (R : CommRingCat.{u}) (h : Spec R ⟶ S)
    (u : (Gm S).obj.obj (op (Over.mk h))) :
    gmObjSpecEquiv S R h ((powHom S n).hom.app _ u) = n • gmObjSpecEquiv S R h u :=
  map_nsmul (gmObjSpecEquiv S R h) n u

/-- The presheaf `T ↦ μ_n(Γ(T, O_T))` underlying `mu S n`. -/
@[expose]
noncomputable def muPresheaf (n : ℕ) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of (Additive (rootsOfUnity n Γ(T.unop.left, ⊤)))
  map f := AddCommGrpCat.ofHom (restrictRootsOfUnity f.unop.left.appTop.hom n).toAdditive
  -- `appTop` of an identity or a composite is definitionally the identity or the composite.
  map_id T := by
    ext u
    exact Subtype.ext (Units.ext rfl)
  map_comp f g := by
    ext u
    exact Subtype.ext (Units.ext rfl)

/-- The inclusion of `n`-th roots of unity into units, as a map of presheaves. -/
noncomputable def muPresheafι (n : ℕ) : muPresheaf S n ⟶ (Gm S).obj where
  app T := AddCommGrpCat.ofHom (rootsOfUnity n Γ(T.unop.left, ⊤)).subtype.toAdditive

lemma muPresheafι_comp_powHom (n : ℕ) : muPresheafι S n ≫ (powHom S n).hom = 0 := by
  ext T u
  exact congrArg Additive.ofMul ((mem_rootsOfUnity n _).mp u.toMul.prop)

/-- Objectwise, the `n`-th roots of unity are the kernel of the `n`-th power map. -/
noncomputable def isLimitMuPresheafKernelFork (n : ℕ) :
    IsLimit (KernelFork.ofι (muPresheafι S n) (muPresheafι_comp_powHom S n)) :=
  evaluationJointlyReflectsLimits _ fun T ↦
    (KernelFork.isLimitMapConeEquiv _ _).symm <|
      KernelFork.IsLimit.ofι _ (KernelFork.map_condition _ _)
        (fun {A} g hg ↦ AddCommGrpCat.ofHom
          { toFun a := Additive.ofMul ⟨(g a).toMul,
              (mem_rootsOfUnity n _).mpr (congrArg Additive.toMul
                (ConcreteCategory.congr_hom hg a))⟩
            map_zero' := Subtype.ext (g.hom.map_zero)
            map_add' a b := Subtype.ext (g.hom.map_add a b) })
        (fun g hg ↦ rfl)
        (fun g hg m hm ↦ by
          ext a
          exact Subtype.ext (ConcreteCategory.congr_hom hm a))

/-- The sheaf `μ_n : T ↦ {t ∈ Γ(T, O_T)ˣ | tⁿ = 1}` of `n`-th roots of unity on the big
fpqc site over `S`, written additively. It is a subsheaf of `𝔾_m` (`muToGm`), the kernel of
the `n`-th power map (`isLimitMuKernelFork`). -/
@[expose]
noncomputable def mu (n : ℕ) : Sheaf (fpqcTopology.over S) AddCommGrpCat.{u} where
  obj := muPresheaf S n
  property := ObjectProperty.prop_of_isLimit (Presheaf.IsSheaf (fpqcTopology.over S))
    (isLimitMuPresheafKernelFork S n) (by rintro (_ | _) <;> exact (Gm S).property)

lemma mu_obj (n : ℕ) (T : Over S) :
    (mu S n).obj.obj (op T) = AddCommGrpCat.of (Additive (rootsOfUnity n Γ(T.left, ⊤))) := rfl

@[simp]
lemma mu_map_apply (n : ℕ) {T T' : Over S} (f : T ⟶ T')
    (u : Additive (rootsOfUnity n Γ(T'.left, ⊤))) :
    (mu S n).obj.map f.op u =
      Additive.ofMul (restrictRootsOfUnity f.left.appTop.hom n u.toMul) := rfl

/-- The value of `μ_n` on an affine `S`-scheme `Spec R` is the group of `n`-th roots of unity
of `R`, written additively. -/
noncomputable def muObjSpecEquiv (n : ℕ) (R : CommRingCat.{u}) (h : Spec R ⟶ S) :
    (mu S n).obj.obj (op (Over.mk h)) ≃+ Additive (rootsOfUnity n R) :=
  -- By `mu_obj` (`rfl`), the value of `μ_n` on `Spec R` is
  -- `Additive (rootsOfUnity n Γ(Spec R, ⊤))`.
  (MulEquiv.toAdditive
      ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv.restrictRootsOfUnity n) :
    Additive (rootsOfUnity n Γ(Spec R, ⊤)) ≃+ Additive (rootsOfUnity n R))

@[simp]
lemma coe_muObjSpecEquiv_apply (n : ℕ) (R : CommRingCat.{u}) (h : Spec R ⟶ S)
    (ζ : Additive (rootsOfUnity n Γ(Spec R, ⊤))) :
    (((muObjSpecEquiv S n R h ζ).toMul : Rˣ) : R) =
      (Scheme.ΓSpecIso R).hom ((ζ.toMul : Γ(Spec R, ⊤)ˣ) : Γ(Spec R, ⊤)) :=
  (rfl)

@[simp]
lemma coe_muObjSpecEquiv_symm_apply (n : ℕ) (R : CommRingCat.{u}) (h : Spec R ⟶ S)
    (ζ : Additive (rootsOfUnity n R)) :
    ((Additive.toMul (α := rootsOfUnity n Γ(Spec R, ⊤)) ((muObjSpecEquiv S n R h).symm ζ) :
      Γ(Spec R, ⊤)ˣ) : Γ(Spec R, ⊤)) =
      (Scheme.ΓSpecIso R).inv ((ζ.toMul : Rˣ) : R) :=
  (rfl)

/-- The inclusion `μ_n ⟶ 𝔾_m`. -/
noncomputable def muToGm (n : ℕ) : mu S n ⟶ Gm S where
  hom := muPresheafι S n

@[simp]
lemma muToGm_app_apply (n : ℕ) (T : Over S) (u : Additive (rootsOfUnity n Γ(T.left, ⊤))) :
    (muToGm S n).hom.app (op T) u = Additive.ofMul (u.toMul : Γ(T.left, ⊤)ˣ) := (rfl)

/-- On an affine test scheme `Spec R`, the inclusion `μ_n ⟶ 𝔾_m` is the inclusion of the
`n`-th roots of unity of `R` into `Rˣ`. -/
lemma gmObjSpecEquiv_muToGm_app (n : ℕ) (R : CommRingCat.{u}) (h : Spec R ⟶ S)
    (ζ : (mu S n).obj.obj (op (Over.mk h))) :
    gmObjSpecEquiv S R h ((muToGm S n).hom.app _ ζ) =
      Additive.ofMul ((muObjSpecEquiv S n R h ζ).toMul : Rˣ) :=
  (rfl)

@[reassoc (attr := simp)]
lemma muToGm_comp_powHom (n : ℕ) : muToGm S n ≫ powHom S n = 0 := by
  ext1
  exact muPresheafι_comp_powHom S n

/-- `μ_n` is the kernel of the `n`-th power map `𝔾_m ⟶ 𝔾_m`. -/
noncomputable def isLimitMuKernelFork (n : ℕ) :
    IsLimit (KernelFork.ofι (muToGm S n) (muToGm_comp_powHom S n)) :=
  isLimitOfReflects (sheafToPresheaf _ _) <|
    (KernelFork.isLimitMapConeEquiv _ _).symm (isLimitMuPresheafKernelFork S n)

/-- **`μ_n` is the kernel in the Kummer sequence.** For every topology `J` on schemes coarser
than the fpqc topology, such as the étale topology, the sheaf `μ_n` on the site `Over S` for `J`
is the kernel of the `n`-th power map `𝔾_m ⟶ 𝔾_m`. -/
@[stacks 03PL]
noncomputable def isLimitMuKernelForkMap (J : GrothendieckTopology Scheme.{u})
    [(𝟭 (Over S)).IsContinuous (J.over S) (fpqcTopology.over S)] (n : ℕ) :
    IsLimit ((KernelFork.ofι (muToGm S n) (muToGm_comp_powHom S n)).map
      ((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over S)
        (fpqcTopology.over S))) :=
  KernelFork.mapIsLimit _ (isLimitMuKernelFork S n) _

/-- `μ_1` is the zero sheaf. -/
lemma isZero_mu_one : IsZero (mu S 1) :=
  IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) _ <|
    Functor.isZero _ fun T ↦
      AddCommGrpCat.isZero_of_subsingleton (.of (Additive (rootsOfUnity 1 Γ(T.unop.left, ⊤))))

end AlgebraicGeometry.Scheme
