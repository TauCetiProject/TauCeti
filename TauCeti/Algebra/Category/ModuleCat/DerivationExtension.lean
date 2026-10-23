/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import TauCeti.Algebra.Category.ModuleCat.Smooth.Basic
public import TauCeti.Algebra.Lie.Derivation.Basic

/-!
# The self-extension of a module attached to a derivation

Let `A` be an `R`-algebra, `δ` a derivation of `A` (an element of
`TauCeti.derivationLieAlgebra R A`) and `M` an `A`-module. The pairs `(u, v)` of elements of `M`
form an `A`-module `E_δ(M)` under
`a • (u, v) = (a • u + δ a • v, a • v)`;
the Leibniz rule `δ (a * b) = δ a * b + a * δ b` is exactly what makes this action associative.
The maps `u ↦ (u, 0)` and `(u, v) ↦ v` are `A`-linear, so `E_δ(M)` is an extension of `M` by
itself:
`0 → M → E_δ(M) → M → 0`.
Writing `(u, v) = v + ε u` with `ε² = 0`, the module `E_δ(M)` is `M[ε]` with `a` acting through
`a + ε δ a`, so it is the first-order deformation of `M` in the direction of `δ`. Changing `δ` by
the inner derivation `ad b = ⁅b, -⁆` does not change the extension: `(u, v) ↦ (u + b • v, v)` is
an isomorphism `E_δ(M) ≅ E_(δ + ad b)(M)` compatible with both maps. These are the extensions
through which outer derivations of `A` give classes in `Ext¹_A(M, M)`; this file constructs the
extensions themselves, not their `Ext` classes.

When `A` carries a topology, `δ` is continuous and `M` is a discrete module, `E_δ(M)` is again
discrete, and the short exact sequence lives in the abelian category of discrete `A`-modules.

## Main definitions

* `TauCeti.DerivationExtension δ M`: the module `E_δ(M)`, with coordinates `fst = u`, `snd = v`.
* `TauCeti.DerivationExtension.inlHom`, `TauCeti.DerivationExtension.sndHom`: the inclusion
  `u ↦ (u, 0)` and the projection `(u, v) ↦ v`.
* `TauCeti.DerivationExtension.map`: functoriality in `M`.
* `TauCeti.DerivationExtension.innerEquiv`: for `δ' = δ + innerDerivation R b`, the isomorphism
  `(u, v) ↦ (u + b • v, v)` from `E_δ(M)` to `E_δ'(M)`.
* `TauCeti.DerivationExtension.shortComplex`: the short complex `M → E_δ(M) → M` in
  `ModuleCat A`, and `TauCeti.DerivationExtension.functor`: the same, as a functor of `M`.
* `TauCeti.DerivationExtension.functorInnerIso`: the natural isomorphism of short complexes
  induced by `innerEquiv`, the identity on both ends.
* `TauCeti.DerivationExtension.discreteShortComplex`: the short complex in the full subcategory
  of discrete modules, for a continuous derivation.

## Main results

* `TauCeti.DerivationExtension.shortExact_shortComplex`: `0 → M → E_δ(M) → M → 0` is short exact.
* `TauCeti.DerivationExtension.innerEquiv_zero`, `TauCeti.DerivationExtension.innerEquiv_trans`:
  the comparison for `b = 0` is the identity, and the comparisons for `b` and `b'` compose to the
  comparison for `b + b'`.
* `TauCeti.discreteModules_derivationExtension`: `E_δ(M)` is discrete when `δ` is continuous and
  `M` is discrete.
* `TauCeti.DerivationExtension.shortExact_discreteShortComplex`: the sequence is short exact in the
  category of discrete modules.

## Implementation notes

`DerivationExtension δ M` is a structure rather than a synonym for `M × M`: the product already
carries the componentwise `A`-module structure, which is a different one. The additive group is
transported from `M × M` along `DerivationExtension.equivProd`.

The bodies of `shortComplex`, `functor` and `discreteShortComplex` are exposed: their objects and
maps are the data a consumer computes with, and their `simps` lemmas are proved by unfolding.

## References

* Edward Frenkel, [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  for the role of first-order deformations of modules over the completed enveloping algebra at
  the critical level.
-/

public section

namespace TauCeti

open CategoryTheory

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A]

/-- The **self-extension** `E_δ(M)` of a module `M` attached to a derivation `δ`: pairs `(u, v)`
of elements of `M`, on which `a` acts by `a • (u, v) = (a • u + δ a • v, a • v)`. The first
coordinate carries the submodule `M` and the second the quotient `M`. -/
@[ext]
structure DerivationExtension (δ : derivationLieAlgebra R A) (M : Type v) where
  /-- The coordinate `u` of `(u, v)`, in which the submodule `M` sits. -/
  fst : M
  /-- The coordinate `v` of `(u, v)`, the image in the quotient `M`. -/
  snd : M

namespace DerivationExtension

section Module

variable (δ : derivationLieAlgebra R A) (M : Type v)

/-- The underlying set of `E_δ(M)` is `M × M`. -/
def equivProd : DerivationExtension δ M ≃ M × M where
  toFun x := (x.fst, x.snd)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equivProd_apply (x : DerivationExtension δ M) : equivProd δ M x = (x.fst, x.snd) :=
  (rfl)

@[simp]
theorem equivProd_symm_apply (x : M × M) : (equivProd δ M).symm x = ⟨x.1, x.2⟩ :=
  (rfl)

variable [AddCommGroup M]

instance : AddCommGroup (DerivationExtension δ M) :=
  (equivProd δ M).addCommGroup

variable {δ M}

@[simp]
theorem fst_zero : (0 : DerivationExtension δ M).fst = 0 :=
  (rfl)

@[simp]
theorem snd_zero : (0 : DerivationExtension δ M).snd = 0 :=
  (rfl)

@[simp]
theorem fst_add (x y : DerivationExtension δ M) : (x + y).fst = x.fst + y.fst :=
  (rfl)

@[simp]
theorem snd_add (x y : DerivationExtension δ M) : (x + y).snd = x.snd + y.snd :=
  (rfl)

@[simp]
theorem fst_neg (x : DerivationExtension δ M) : (-x).fst = -x.fst :=
  (rfl)

@[simp]
theorem snd_neg (x : DerivationExtension δ M) : (-x).snd = -x.snd :=
  (rfl)

@[simp]
theorem fst_sub (x y : DerivationExtension δ M) : (x - y).fst = x.fst - y.fst :=
  (rfl)

@[simp]
theorem snd_sub (x y : DerivationExtension δ M) : (x - y).snd = x.snd - y.snd :=
  (rfl)

variable [Module A M]

instance : SMul A (DerivationExtension δ M) where
  smul a x := ⟨a • x.fst + (δ : Module.End R A) a • x.snd, a • x.snd⟩

@[simp]
theorem fst_smul (a : A) (x : DerivationExtension δ M) :
    (a • x).fst = a • x.fst + (δ : Module.End R A) a • x.snd :=
  (rfl)

@[simp]
theorem snd_smul (a : A) (x : DerivationExtension δ M) : (a • x).snd = a • x.snd :=
  (rfl)

instance : Module A (DerivationExtension δ M) where
  one_smul x := by ext <;> simp
  mul_smul a b x := by
    ext
    · simp only [fst_smul, snd_smul, derivationLieAlgebra.leibniz, add_smul, mul_smul, smul_add]
      abel
    · simp [mul_smul]
  smul_zero a := by ext <;> simp
  smul_add a x y := by
    ext
    · simp only [fst_smul, fst_add, snd_add, smul_add]
      abel
    · simp [smul_add]
  add_smul a b x := by
    ext
    · simp only [fst_smul, fst_add, map_add, add_smul]
      abel
    · simp [add_smul]
  zero_smul x := by ext <;> simp

end Module

section Maps

variable (δ : derivationLieAlgebra R A) (M : Type v) [AddCommGroup M] [Module A M]

/-- The inclusion `u ↦ (u, 0)` of the submodule `M` into `E_δ(M)`. -/
def inlHom : M →ₗ[A] DerivationExtension δ M where
  toFun u := ⟨u, 0⟩
  map_add' u u' := by ext <;> simp
  map_smul' a u := by ext <;> simp

@[simp]
theorem fst_inlHom (u : M) : (inlHom δ M u).fst = u :=
  (rfl)

@[simp]
theorem snd_inlHom (u : M) : (inlHom δ M u).snd = 0 :=
  (rfl)

/-- The projection `(u, v) ↦ v` of `E_δ(M)` onto the quotient `M`. -/
def sndHom : DerivationExtension δ M →ₗ[A] M where
  toFun := snd
  map_add' := snd_add
  map_smul' := snd_smul

@[simp]
theorem sndHom_apply (x : DerivationExtension δ M) : sndHom δ M x = x.snd :=
  (rfl)

theorem inlHom_injective : Function.Injective (inlHom δ M) :=
  fun _ _ h => congrArg fst h

theorem sndHom_surjective : Function.Surjective (sndHom δ M) :=
  fun v => ⟨⟨0, v⟩, (rfl)⟩

@[simp]
theorem sndHom_comp_inlHom : sndHom δ M ∘ₗ inlHom δ M = 0 :=
  LinearMap.ext fun _ => (rfl)

/-- `E_δ(M)` is an extension of `M` by `M`: the kernel of the projection is the image of the
inclusion. -/
theorem exact_inlHom_sndHom : Function.Exact (inlHom δ M) (sndHom δ M) := by
  intro x
  refine ⟨fun hx => ⟨x.fst, ?_⟩, ?_⟩
  · ext
    · simp
    · simpa using hx.symm
  · rintro ⟨u, rfl⟩
    simp

variable {δ M} {N : Type w} [AddCommGroup N] [Module A N]

/-- The functoriality of `E_δ(-)`: a linear map `f` acts coordinatewise. -/
def map (f : M →ₗ[A] N) : DerivationExtension δ M →ₗ[A] DerivationExtension δ N where
  toFun x := ⟨f x.fst, f x.snd⟩
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

@[simp]
theorem fst_map (f : M →ₗ[A] N) (x : DerivationExtension δ M) : (map f x).fst = f x.fst :=
  (rfl)

@[simp]
theorem snd_map (f : M →ₗ[A] N) (x : DerivationExtension δ M) : (map f x).snd = f x.snd :=
  (rfl)

@[simp]
theorem map_id : map (δ := δ) (LinearMap.id : M →ₗ[A] M) = LinearMap.id :=
  (rfl)

theorem map_comp {P : Type*} [AddCommGroup P] [Module A P] (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    map (δ := δ) (g ∘ₗ f) = map g ∘ₗ map f :=
  (rfl)

theorem map_comp_inlHom (f : M →ₗ[A] N) : map f ∘ₗ inlHom δ M = inlHom δ N ∘ₗ f := by
  ext u <;> simp

theorem sndHom_comp_map (f : M →ₗ[A] N) : sndHom δ N ∘ₗ map f = f ∘ₗ sndHom δ M :=
  (rfl)

end Maps

section Inner

variable {δ δ' δ'' : derivationLieAlgebra R A} {b b' : A} (M : Type v) [AddCommGroup M]
  [Module A M]

/-- Changing a derivation by an inner derivation does not change its self-extension: when
`δ' = δ + ad b`, the map `(u, v) ↦ (u + b • v, v)` is an isomorphism `E_δ(M) ≃ E_δ'(M)`. -/
def innerEquiv (h : δ' = δ + innerDerivation R b) :
    DerivationExtension δ M ≃ₗ[A] DerivationExtension δ' M where
  toFun x := ⟨x.fst + b • x.snd, x.snd⟩
  invFun x := ⟨x.fst - b • x.snd, x.snd⟩
  map_add' x y := by
    ext
    · simp only [fst_add, snd_add, smul_add]
      abel
    · simp
  map_smul' a x := by
    have hδ' : (δ' : Module.End R A) a = (δ : Module.End R A) a + (b * a - a * b) := by
      simp [h, Ring.lie_def]
    ext
    · simp only [fst_smul, snd_smul, RingHom.id_apply, hδ', add_smul, sub_smul, mul_smul,
        smul_add]
      abel
    · simp
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

@[simp]
theorem fst_innerEquiv (h : δ' = δ + innerDerivation R b) (x : DerivationExtension δ M) :
    (innerEquiv M h x).fst = x.fst + b • x.snd :=
  (rfl)

@[simp]
theorem snd_innerEquiv (h : δ' = δ + innerDerivation R b) (x : DerivationExtension δ M) :
    (innerEquiv M h x).snd = x.snd :=
  (rfl)

@[simp]
theorem fst_innerEquiv_symm (h : δ' = δ + innerDerivation R b) (x : DerivationExtension δ' M) :
    ((innerEquiv M h).symm x).fst = x.fst - b • x.snd :=
  (rfl)

@[simp]
theorem snd_innerEquiv_symm (h : δ' = δ + innerDerivation R b) (x : DerivationExtension δ' M) :
    ((innerEquiv M h).symm x).snd = x.snd :=
  (rfl)

/-- The comparison `innerEquiv` restricts to the identity on the submodule `M`. -/
@[simp]
theorem innerEquiv_comp_inlHom (h : δ' = δ + innerDerivation R b) :
    (innerEquiv M h : DerivationExtension δ M →ₗ[A] DerivationExtension δ' M) ∘ₗ inlHom δ M =
      inlHom δ' M := by
  ext u <;> simp

/-- The comparison `innerEquiv` induces the identity on the quotient `M`. -/
@[simp]
theorem sndHom_comp_innerEquiv (h : δ' = δ + innerDerivation R b) :
    sndHom δ' M ∘ₗ (innerEquiv M h : DerivationExtension δ M →ₗ[A] DerivationExtension δ' M) =
      sndHom δ M :=
  (rfl)

/-- The comparison `innerEquiv` is natural in `M`. -/
theorem map_comp_innerEquiv {N : Type w} [AddCommGroup N] [Module A N]
    (h : δ' = δ + innerDerivation R b) (f : M →ₗ[A] N) :
    map f ∘ₗ (innerEquiv M h : DerivationExtension δ M →ₗ[A] DerivationExtension δ' M) =
      (innerEquiv N h : DerivationExtension δ N →ₗ[A] DerivationExtension δ' N) ∘ₗ map f := by
  ext x <;> simp

/-- The comparison for the zero inner derivation is the identity. -/
@[simp]
theorem innerEquiv_zero (h : δ = δ + innerDerivation R (0 : A)) :
    innerEquiv M h = LinearEquiv.refl A (DerivationExtension δ M) := by
  ext x <;> simp

/-- The comparisons for `b` and `b'` compose to the comparison for `b + b'`. -/
theorem innerEquiv_trans (h : δ' = δ + innerDerivation R b) (h' : δ'' = δ' + innerDerivation R b') :
    (innerEquiv M h).trans (innerEquiv M h') =
      innerEquiv M (b := b + b') (by rw [h', h, map_add, add_assoc]) := by
  ext x <;> simp [add_smul, add_assoc]

/-- The inverse of the comparison for `b` is the comparison for `-b`. -/
theorem innerEquiv_symm (h : δ' = δ + innerDerivation R b) :
    (innerEquiv M h).symm = innerEquiv M (b := -b) (by rw [h, map_neg, add_neg_cancel_right]) := by
  ext x <;> simp [sub_eq_add_neg]

end Inner

section ShortComplex

variable (δ : derivationLieAlgebra R A) (M : ModuleCat.{v} A)

/-- The self-extension `0 → M → E_δ(M) → M → 0`, as a short complex in `ModuleCat A`. -/
@[expose, simps]
def shortComplex : ShortComplex (ModuleCat.{v} A) where
  X₁ := M
  X₂ := ModuleCat.of A (DerivationExtension δ M)
  X₃ := M
  f := ModuleCat.ofHom (inlHom δ M)
  g := ModuleCat.ofHom (sndHom δ M)
  zero := ModuleCat.hom_ext (sndHom_comp_inlHom δ M)

/-- The self-extension of `M` attached to a derivation is a short exact sequence. -/
theorem shortExact_shortComplex : (shortComplex δ M).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (exact_inlHom_sndHom δ M) (inlHom_injective δ M)
    (sndHom_surjective δ M)

/-- The self-extension `0 → M → E_δ(M) → M → 0`, as a functor of `M`. -/
@[expose, simps]
def functor : ModuleCat.{v} A ⥤ ShortComplex (ModuleCat.{v} A) where
  obj M := shortComplex δ M
  map f :=
    { τ₁ := f
      τ₂ := ModuleCat.ofHom (map f.hom)
      τ₃ := f
      comm₁₂ := ModuleCat.hom_ext (map_comp_inlHom (δ := δ) f.hom).symm
      comm₂₃ := ModuleCat.hom_ext (sndHom_comp_map (δ := δ) f.hom) }

variable {δ} {δ' : derivationLieAlgebra R A} {b : A}

/-- When `δ' = δ + ad b`, the self-extensions attached to `δ` and `δ'` are isomorphic as
extensions, naturally in `M`: the isomorphism is `innerEquiv` in the middle and the identity on
both ends. -/
def functorInnerIso (h : δ' = δ + innerDerivation R b) : functor δ ≅ functor δ' :=
  NatIso.ofComponents
    (fun M => ShortComplex.isoMk (Iso.refl _) (innerEquiv M h).toModuleIso (Iso.refl _)
      (ModuleCat.hom_ext (innerEquiv_comp_inlHom M h).symm)
      (ModuleCat.hom_ext (sndHom_comp_innerEquiv M h)))
    (fun f => by
      ext : 1
      · exact (Category.comp_id f).trans (Category.id_comp f).symm
      · exact ModuleCat.hom_ext (map_comp_innerEquiv _ h f.hom).symm
      · exact (Category.comp_id f).trans (Category.id_comp f).symm)

@[simp]
theorem functorInnerIso_hom_app_τ₂ (h : δ' = δ + innerDerivation R b) :
    ((functorInnerIso h).hom.app M).τ₂ = ModuleCat.ofHom (innerEquiv M h).toLinearMap :=
  (rfl)

@[simp]
theorem functorInnerIso_hom_app_τ₁ (h : δ' = δ + innerDerivation R b) :
    ((functorInnerIso h).hom.app M).τ₁ = 𝟙 M :=
  (rfl)

@[simp]
theorem functorInnerIso_hom_app_τ₃ (h : δ' = δ + innerDerivation R b) :
    ((functorInnerIso h).hom.app M).τ₃ = 𝟙 M :=
  (rfl)

@[simp]
theorem functorInnerIso_inv_app_τ₂ (h : δ' = δ + innerDerivation R b) :
    ((functorInnerIso h).inv.app M).τ₂ = ModuleCat.ofHom (innerEquiv M h).symm.toLinearMap :=
  (rfl)

@[simp]
theorem functorInnerIso_inv_app_τ₁ (h : δ' = δ + innerDerivation R b) :
    ((functorInnerIso h).inv.app M).τ₁ = 𝟙 M :=
  (rfl)

@[simp]
theorem functorInnerIso_inv_app_τ₃ (h : δ' = δ + innerDerivation R b) :
    ((functorInnerIso h).inv.app M).τ₃ = 𝟙 M :=
  (rfl)

end ShortComplex

end DerivationExtension

section Discrete

variable [TopologicalSpace A] {δ : derivationLieAlgebra R A}

/-- The self-extension of a discrete module along a continuous derivation is discrete. -/
theorem discreteModules_derivationExtension (hδ : Continuous (δ : Module.End R A))
    {M : ModuleCat.{v} A} (hM : discreteModules A M) :
    discreteModules A (ModuleCat.of A (DerivationExtension δ M)) := by
  rw [discreteModules_iff_isOpen]
  intro x y
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hfst : Continuous fun a : A => a • x.fst + (δ : Module.End R A) a • x.snd :=
    (discreteModules_iff.1 hM x.fst).add ((discreteModules_iff.1 hM x.snd).comp hδ)
  have : {a : A | a • x = y} =
      (fun a : A => a • x.fst + (δ : Module.End R A) a • x.snd) ⁻¹' {y.fst} ∩
        {a | a • x.snd = y.snd} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      DerivationExtension.ext_iff, DerivationExtension.fst_smul, DerivationExtension.snd_smul]
  rw [this]
  exact (hfst.isOpen_preimage _ (isOpen_discrete _)).inter
    (discreteModules_iff_isOpen.1 hM x.snd y.snd)

namespace DerivationExtension

variable (hδ : Continuous (δ : Module.End R A)) (M : (discreteModules.{v} A).FullSubcategory)

/-- For a continuous derivation `δ` and a discrete module `M`, the self-extension
`0 → M → E_δ(M) → M → 0`, as a short complex in the category of discrete modules. -/
@[expose, simps]
def discreteShortComplex : ShortComplex (discreteModules.{v} A).FullSubcategory where
  X₁ := M
  X₂ := ⟨ModuleCat.of A (DerivationExtension δ M.obj),
    discreteModules_derivationExtension hδ M.property⟩
  X₃ := M
  f := ObjectProperty.homMk (shortComplex δ M.obj).f
  g := ObjectProperty.homMk (shortComplex δ M.obj).g
  zero := InducedCategory.hom_ext (shortComplex δ M.obj).zero

/-- The inclusion of discrete modules sends `discreteShortComplex` to `shortComplex`. -/
@[simp]
theorem discreteShortComplex_map_ι :
    (discreteShortComplex hδ M).map (discreteModules.{v} A).ι = shortComplex δ M.obj :=
  (rfl)

/-- The self-extension of a discrete module along a continuous derivation is short exact in the
category of discrete modules. -/
theorem shortExact_discreteShortComplex : (discreteShortComplex hδ M).ShortExact :=
  ShortExact.reflects_shortExact_of_faithful (discreteModules.{v} A).ι
    (by simpa using shortExact_shortComplex δ M.obj)

end DerivationExtension

end Discrete

end TauCeti
