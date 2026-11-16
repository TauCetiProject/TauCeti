/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Projective
import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Projective dimension under `Tor`-acyclic base change and homological epimorphisms

Let `A` be a commutative ring and `B` an `A`-algebra. When `B` is flat over `A`, base change does
not increase projective dimension (`ModuleCat.hasProjectiveDimensionLT_tensorProduct`). More
generally, if an individual `A`-module `N` is `Tor`-acyclic against `B`, meaning
`Tor_{k+1}^A(N, B) = 0` for every `k`, then base change still does not increase the projective
dimension of `N`:

```text
pd_B (B ⊗[A] N) ≤ pd_A N.
```

Indeed, for a projective presentation `0 → K → Q → N → 0` over `A`, the vanishing of
`Tor_1^A(N, B)` keeps `0 → B ⊗[A] K → B ⊗[A] Q → B ⊗[A] N → 0` short exact, while the vanishing of
`Tor_{k+2}^A(N, B)` and of `Tor_{k+1}^A(Q, B)` makes `K` again `Tor`-acyclic against `B`. Since
`B ⊗[A] Q` is projective over `B`, induction on the projective dimension of `N` concludes.

Now suppose that `B` is commutative and `A → B` is a **homological epimorphism**: `B`-scalars move
across the tensor sign in `B ⊗[A] B` (so `B ⊗[A] B ≃ B` via multiplication; this holds in
particular for every surjective ring homomorphism, by
`TensorProduct.CompatibleSMul.of_algebraMap_surjective`), and `Tor_{k+1}^A(B, B) = 0` for every
`k`. Then every `B`-module `M` satisfies `B ⊗[A] M ≃ M` and `Tor_{k+1}^A(M, B) = 0` for every `k`
(by induction on `k` along a free `B`-presentation of `M`, using that `Tor` commutes with direct
sums). Consequently,

```text
pd_B M ≤ pd_A M
```

for every `B`-module `M`. In particular, a global dimension bound over `A` passes to `B`.

## Main results

* `ModuleCat.hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor`: if `Tor_{k+1}^A(N, B) = 0` for
  all `k`, then `pd_A N < n` implies `pd_B (B ⊗[A] N) < n`.
* `ModuleCat.projectiveDimension_tensorProduct_le_of_isZero_Tor`: the corresponding inequality
  `pd_B (B ⊗[A] N) ≤ pd_A N`.
* `ModuleCat.isZero_Tor_succ_restrictScalars_of_compatibleSMul`: along a homological epimorphism
  `A → B`, every `B`-module `M` satisfies `Tor_{k+1}^A(M, B) = 0`.
* `ModuleCat.hasProjectiveDimensionLT_of_restrictScalars_of_isZero_Tor`: along a homological
  epimorphism `A → B`, `pd_A M < n` implies `pd_B M < n` for every `B`-module `M`.
* `ModuleCat.projectiveDimension_le_restrictScalars_of_isZero_Tor`: the corresponding inequality
  `pd_B M ≤ pd_A M`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), proof of Proposition 11.31.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 3.2.
-/

public section

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

universe u

namespace ModuleCat

section BaseChange

variable {A : Type u} [CommRing A] (B : Type u) [Ring B] [Algebra A B]

/-- The degree-wise induction proving `hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor`. -/
private theorem hasProjectiveDimensionLE_tensorProduct_of_isZero_Tor (d : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module A N],
      HasProjectiveDimensionLE (of A N) d →
      (∀ k, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A N)).obj (of A B))) →
      HasProjectiveDimensionLE (of B (B ⊗[A] N)) d := by
  induction d with
  | zero =>
    intro N _ _ hpd _
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at hpd ⊢
    infer_instance
  | succ d ih =>
    intro N _ _ hpd hTor
    let Q := Projective.over (of A N)
    let f : Q →ₗ[A] N := (Projective.π (of A N)).hom
    have hf : Function.Surjective f := (epi_iff_surjective _).mp inferInstance
    have hS : f.shortComplexKer.ShortExact := f.shortExact_shortComplexKer hf
    have hpdK : HasProjectiveDimensionLE (of A (LinearMap.ker f)) d :=
      (f.hasProjectiveDimensionLE_succ_iff_ker hf d).mp hpd
    have hQflat : Module.Flat A Q := Module.Flat.of_projective
    have hTorK (k : ℕ) :
        IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A (LinearMap.ker f))).obj (of A B)) :=
      hS.isZero_Tor_X₁ (of A B) (hTor (k + 1)) (isZero_Tor_succ_of_flat Q (of A B) k)
    -- Vanishing of `Tor₁(N, B)` makes `B ⊗[A] ker f → B ⊗[A] Q` injective, so it identifies
    -- `B ⊗[A] ker f` with the kernel of the surjection `B ⊗[A] Q → B ⊗[A] N`.
    have hinjR : Function.Injective ((LinearMap.ker f).subtype.rTensor B) :=
      hS.injective_rTensor_of_isZero_Tor_one (of A B) (hTor 0)
    have hinjL :
        Function.Injective (AlgebraTensorModule.lTensor B B (LinearMap.ker f).subtype) := by
      have hcomm : (TensorProduct.comm A B Q).toLinearMap ∘ₗ
            (LinearMap.ker f).subtype.lTensor B =
          (LinearMap.ker f).subtype.rTensor B ∘ₗ
            (TensorProduct.comm A B (LinearMap.ker f)).toLinearMap := by
        ext b k
        rfl
      have hfun : (TensorProduct.comm A B Q) ∘ AlgebraTensorModule.lTensor B B
            (LinearMap.ker f).subtype =
          (LinearMap.ker f).subtype.rTensor B ∘ TensorProduct.comm A B (LinearMap.ker f) :=
        funext fun x ↦ LinearMap.congr_fun hcomm x
      exact (EquivLike.comp_injective _ (TensorProduct.comm A B Q)).1 <|
        hfun ▸ hinjR.comp (TensorProduct.comm A B (LinearMap.ker f)).injective
    have hrange : LinearMap.range (AlgebraTensorModule.lTensor B B (LinearMap.ker f).subtype) =
        LinearMap.ker (AlgebraTensorModule.lTensor B B f) := by
      have hex := LinearMap.exact_iff.1 (lTensor_exact B (LinearMap.exact_subtype_ker_map f) hf)
      ext x
      exact (SetLike.ext_iff.1 hex x).symm
    let eKer : B ⊗[A] LinearMap.ker f ≃ₗ[B]
        LinearMap.ker (AlgebraTensorModule.lTensor B B f) :=
      (LinearEquiv.ofInjective _ hinjL).trans (LinearEquiv.ofEq _ _ hrange)
    rw [(AlgebraTensorModule.lTensor B B f).hasProjectiveDimensionLE_succ_iff_ker
      (LinearMap.lTensor_surjective B hf)]
    have := ih (LinearMap.ker f) hpdK hTorK
    exact hasProjectiveDimensionLT_of_iso eKer.toModuleIso (d + 1)

/-- **Base change of projective dimension for `Tor`-acyclic modules.** If `Tor_{k+1}^A(N, B) = 0`
for all `k` and `N` has projective dimension `< n` over `A`, then `B ⊗[A] N` has projective
dimension `< n` over `B`. -/
theorem hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor
    (N : Type u) [AddCommGroup N] [Module A N] {n : ℕ}
    (hpd : HasProjectiveDimensionLT (of A N) n)
    (hTor : ∀ k, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A N)).obj (of A B))) :
    HasProjectiveDimensionLT (of B (B ⊗[A] N)) n := by
  cases n with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero, isZero_iff_subsingleton] at hpd ⊢
    infer_instance
  | succ d =>
    exact hasProjectiveDimensionLE_tensorProduct_of_isZero_Tor B d N hpd hTor

/-- **Base change does not increase the projective dimension of a `Tor`-acyclic module**:
if `Tor_{k+1}^A(N, B) = 0` for all `k`, then `pd_B (B ⊗[A] N) ≤ pd_A N`. -/
theorem projectiveDimension_tensorProduct_le_of_isZero_Tor
    (N : Type u) [AddCommGroup N] [Module A N]
    (hTor : ∀ k, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A N)).obj (of A B))) :
    projectiveDimension (of B (B ⊗[A] N)) ≤ projectiveDimension (of A N) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ h ↦
    hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor B N h hTor

end BaseChange

section HomologicalEpimorphism

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [TensorProduct.CompatibleSMul A B B B]

/-- **Higher `Tor` vanishes for all modules over a homological epimorphism.** If `B`-scalars move
across the tensor sign in `B ⊗[A] B` (for instance if `A → B` is surjective) and
`Tor_{k+1}^A(B, B) = 0` for every `k`, then `Tor_{k+1}^A(M, B) = 0` for every `B`-module `M` and
every `k`. -/
theorem isZero_Tor_succ_restrictScalars_of_compatibleSMul
    (hB : ∀ k, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A B)).obj (of A B)))
    (M : ModuleCat.{u} B) (k : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj
      ((restrictScalars (algebraMap A B)).obj M)).obj (of A B)) := by
  induction k generalizing M with
  | zero =>
    let f : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
    have hf : Function.Surjective f := fun m ↦ ⟨Finsupp.single m 1, by simp [f]⟩
    -- Present `M` by a free `B`-module `M →₀ B` and restrict scalars to `A`.
    let S := (restrictScalars (algebraMap A B)).mapShortComplex.obj f.shortComplexKer
    have hS : S.ShortExact :=
      shortComplex_shortExact S (LinearMap.exact_subtype_ker_map f) Subtype.val_injective hf
    let isoG : S.X₂ ≅ of A (M →₀ B) := restrictScalarsAlgebraMapIso (R := A) (S := B) (M →₀ B)
    have hfree : IsZero (((Tor (ModuleCat.{u} A) 1).obj S.X₂).obj (of A B)) :=
      (isZero_Tor_finsupp (ι := M) (of A B) (of A B) (hB 0)).of_iso
        (((Tor (ModuleCat.{u} A) 1).mapIso isoG).app (of A B))
    -- `ker f ⊗[A] B ≃ ker f` and `(M →₀ B) ⊗[A] B ≃ (M →₀ B)` compatibly with inclusion.
    have : TensorProduct.CompatibleSMul A B B (LinearMap.ker f) := .of_compatibleSMul_self
    have : TensorProduct.CompatibleSMul A B B (M →₀ B) := .of_compatibleSMul_self
    let isoK : S.X₁ ≅ of A (LinearMap.ker f) :=
      restrictScalarsAlgebraMapIso (R := A) (S := B) (LinearMap.ker f)
    let eK : S.X₁ ⊗[A] B ≃ₗ[A] LinearMap.ker f :=
      (TensorProduct.congr isoK.toLinearEquiv (.refl A B)).trans
        ((TensorProduct.comm A (LinearMap.ker f) B).trans
          ((TensorProduct.lidOfCompatibleSMul A B (LinearMap.ker f)).restrictScalars A))
    let eG : S.X₂ ⊗[A] B ≃ₗ[A] (M →₀ B) :=
      (TensorProduct.congr isoG.toLinearEquiv (.refl A B)).trans
        ((TensorProduct.comm A (M →₀ B) B).trans
          ((TensorProduct.lidOfCompatibleSMul A B (M →₀ B)).restrictScalars A))
    have hcomm : eG.toLinearMap ∘ₗ S.f.hom.rTensor B =
        ((LinearMap.ker f).subtype.restrictScalars A) ∘ₗ eK.toLinearMap :=
      TensorProduct.ext' fun x b ↦ by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
          LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, TensorProduct.congr_tmul,
          TensorProduct.comm_tmul, TensorProduct.lidOfCompatibleSMul_tmul, LinearEquiv.refl_apply,
          eG, eK, isoG, isoK, LinearMap.restrictScalars_apply, Submodule.coe_subtype,
          Submodule.coe_smul]
        refine congrArg (b • ·) ?_
        exact (restrictScalarsAlgebraMapIso_hom_apply (R := A) (S := B) (M →₀ B)
          (x : LinearMap.ker f).1).trans
          (congrArg Subtype.val
            (restrictScalarsAlgebraMapIso_hom_apply (R := A) (S := B) (LinearMap.ker f) x)).symm
    have hinj : Function.Injective (S.f.hom.rTensor B) := by
      have hfun : eG ∘ S.f.hom.rTensor B = (LinearMap.ker f).subtype ∘ eK :=
        funext fun t ↦ LinearMap.congr_fun hcomm t
      exact (EquivLike.comp_injective _ eG).1 <|
        hfun ▸ Subtype.val_injective.comp eK.injective
    exact hS.isZero_Tor_one_X₃ (of A B) hfree hinj
  | succ k ih =>
    let f : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
    have hf : Function.Surjective f := fun m ↦ ⟨Finsupp.single m 1, by simp [f]⟩
    let S := (restrictScalars (algebraMap A B)).mapShortComplex.obj f.shortComplexKer
    have hS : S.ShortExact :=
      shortComplex_shortExact S (LinearMap.exact_subtype_ker_map f) Subtype.val_injective hf
    let isoG : S.X₂ ≅ of A (M →₀ B) := restrictScalarsAlgebraMapIso (R := A) (S := B) (M →₀ B)
    have hfree : IsZero (((Tor (ModuleCat.{u} A) (k + 2)).obj S.X₂).obj (of A B)) :=
      (isZero_Tor_finsupp (ι := M) (of A B) (of A B) (hB (k + 1))).of_iso
        (((Tor (ModuleCat.{u} A) (k + 2)).mapIso isoG).app (of A B))
    exact hS.isZero_Tor_succ_X₃ (of A B) hfree (ih (of B (LinearMap.ker f)))

/-- **Projective dimension does not increase along a homological epimorphism.** If `B`-scalars move
across the tensor sign in `B ⊗[A] B` (for instance if `A → B` is surjective) and
`Tor_{k+1}^A(B, B) = 0` for every `k`, then every `B`-module `M` of projective dimension `< n` over
`A` also has projective dimension `< n` over `B`. -/
theorem hasProjectiveDimensionLT_of_restrictScalars_of_isZero_Tor
    (hB : ∀ k, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A B)).obj (of A B)))
    (M : ModuleCat.{u} B) {n : ℕ}
    (h : HasProjectiveDimensionLT ((restrictScalars (algebraMap A B)).obj M) n) :
    HasProjectiveDimensionLT M n := by
  let : Module A M := Module.compHom M (algebraMap A B)
  have : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : TensorProduct.CompatibleSMul A B B M := .of_compatibleSMul_self
  let isoM : (restrictScalars (algebraMap A B)).obj M ≅ of A M :=
    restrictScalarsAlgebraMapIso (R := A) (S := B) M
  have hM : HasProjectiveDimensionLT (of A M) n := hasProjectiveDimensionLT_of_iso isoM n
  have hBM : HasProjectiveDimensionLT (of B (B ⊗[A] M)) n :=
    hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor B M hM fun k ↦
      (isZero_Tor_succ_restrictScalars_of_compatibleSMul hB M k).of_iso
        (((Tor (ModuleCat.{u} A) (k + 1)).mapIso isoM).app (of A B))
  exact hasProjectiveDimensionLT_of_iso (TensorProduct.lidOfCompatibleSMul A B M).toModuleIso n

/-- **Projective dimension does not increase along a homological epimorphism**:
`pd_B M ≤ pd_A M` for every `B`-module `M`. -/
theorem projectiveDimension_le_restrictScalars_of_isZero_Tor
    (hB : ∀ k, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A B)).obj (of A B)))
    (M : ModuleCat.{u} B) :
    projectiveDimension M ≤ projectiveDimension ((restrictScalars (algebraMap A B)).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ h ↦
    hasProjectiveDimensionLT_of_restrictScalars_of_isZero_Tor hB M h

end HomologicalEpimorphism

end ModuleCat
