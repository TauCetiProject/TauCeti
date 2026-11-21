/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import TauCeti.RingTheory.WittVector.Dieudonne.Ring

/-!
# Dieudonné modules

Let `k` be a perfect ring of characteristic `p`, let `W = W(k)` be its ring of Witt vectors and
let `σ` be the Frobenius automorphism of `W`. A *Dieudonné module* is a `W`-module `M` together
with a `σ`-semilinear map `F : M → M` (the Frobenius) and a `σ⁻¹`-semilinear map `V : M → M`
(the Verschiebung) such that `F V = V F = p`. Over a perfect field, Dieudonné modules of finite
length classify finite commutative `p`-group schemes, contravariantly.

The defining relations of a Dieudonné module are those of the Dieudonné ring
`D_k = W[F, V]` (`TauCeti.DieudonneRing`), and we show that Dieudonné modules are the same as
left `D_k`-modules: the category of Dieudonné modules is equivalent to `ModuleCat D_k`. Both
descriptions are needed: the classification is stated with `W`-lengths and the semilinear maps
`F` and `V`, while Dieudonné modules of group schemes arise as left `D_k`-modules, from the
action of `D_k` on the Witt group schemes.

## Main definitions and results

* `TauCeti.DieudonneModule p k`: the category of Dieudonné modules over `k`; morphisms
  (`TauCeti.DieudonneModule.Hom`) are `W`-linear maps commuting with `F` and `V`.
* `TauCeti.DieudonneModule.isoMk`: an isomorphism of Dieudonné modules from a linear equivalence
  commuting with `F` and `V`.
* `TauCeti.DieudonneModule.instModuleDieudonneRing`: the left `D_k`-module structure of a
  Dieudonné module, in which `C ξ`, `F` and `V` act by `ξ • ·`, `M.F` and `M.V`
  (`TauCeti.DieudonneModule.C_smul`, `TauCeti.DieudonneModule.F_smul`,
  `TauCeti.DieudonneModule.V_smul`); morphisms are `D_k`-linear
  (`TauCeti.DieudonneModule.Hom.map_smul`).
* `TauCeti.DieudonneModule.ofModule`: a left `D_k`-module as a Dieudonné module.
* `TauCeti.DieudonneModule.equivModuleCat`: the equivalence between Dieudonné modules and left
  `D_k`-modules.
* `TauCeti.DieudonneModule.span_range_F`: since `σ` is bijective, the submodule `F M` generated
  by the image of `F` is that image; similarly for `V` (`TauCeti.DieudonneModule.span_range_V`).

## References

* R. Pink, *Finite group schemes*, lecture course WS 2004/05, ETH Zürich lecture notes,
  §23, Definition, p. 54, <https://people.math.ethz.ch/~pink/ftp/FGS/CompleteNotes.pdf>.
* C.-F. Yu, *Introduction to Dieudonné modules and supersingular abelian varieties revisited*,
  arXiv:2603.11506, §2.1, Definition 1.
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory WittVector

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [PerfectRing k p]

local notation "𝕎" => WittVector p

/-- A **Dieudonné module** over a perfect ring `k` of characteristic `p`: a `𝕎 k`-module `M` with
a Frobenius `F : M → M`, semilinear for the Frobenius automorphism `σ` of `𝕎 k`, and a
Verschiebung `V : M → M`, semilinear for `σ⁻¹`, such that `F V = V F = p`. Equivalently
(`TauCeti.DieudonneModule.equivModuleCat`), a left module over the Dieudonné ring. -/
structure DieudonneModule where
  /-- The underlying type of a Dieudonné module. -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module (𝕎 k) carrier]
  /-- The Frobenius of a Dieudonné module, semilinear for the Frobenius `σ` of `𝕎 k`. -/
  F : carrier →ₛₗ[(frobeniusEquiv p k : 𝕎 k →+* 𝕎 k)] carrier
  /-- The Verschiebung of a Dieudonné module, semilinear for the inverse `σ⁻¹` of the Frobenius of
  `𝕎 k`. -/
  V : carrier →ₛₗ[((frobeniusEquiv p k).symm : 𝕎 k →+* 𝕎 k)] carrier
  /-- `F V = p`. -/
  F_V (x : carrier) : F (V x) = (p : 𝕎 k) • x
  /-- `V F = p`. -/
  V_F (x : carrier) : V (F x) = (p : 𝕎 k) • x

namespace DieudonneModule

attribute [instance] isAddCommGroup isModule

attribute [simp] F_V V_F

instance : CoeSort (DieudonneModule.{v} p k) (Type v) :=
  ⟨carrier⟩

variable {p k}

/-! ### The category of Dieudonné modules -/

/-- A morphism of Dieudonné modules: a `𝕎 k`-linear map commuting with `F` and `V`. -/
@[ext]
structure Hom (M N : DieudonneModule.{v} p k) where
  /-- The underlying linear map of a morphism of Dieudonné modules. -/
  hom : M →ₗ[𝕎 k] N
  map_F' (x : M) : hom (M.F x) = N.F (hom x)
  map_V' (x : M) : hom (M.V x) = N.V (hom x)

instance : Category (DieudonneModule.{v} p k) where
  Hom := Hom
  id M := ⟨LinearMap.id, fun _ ↦ rfl, fun _ ↦ rfl⟩
  comp f g := ⟨g.hom ∘ₗ f.hom, fun x ↦ by simp [f.map_F', g.map_F'],
    fun x ↦ by simp [f.map_V', g.map_V']⟩

variable {M N P : DieudonneModule.{v} p k}

@[ext]
theorem hom_ext {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

theorem hom_injective : Function.Injective (fun f : M ⟶ N ↦ f.hom) := fun _ _ ↦ hom_ext

@[simp]
theorem id_hom (M : DieudonneModule.{v} p k) : (𝟙 M : M ⟶ M).hom = LinearMap.id :=
  rfl

@[simp]
theorem comp_hom (f : M ⟶ N) (g : N ⟶ P) : (f ≫ g).hom = g.hom ∘ₗ f.hom :=
  rfl

/-- A morphism of Dieudonné modules commutes with the Frobenius. -/
@[simp]
theorem Hom.map_F (f : M ⟶ N) (x : M) : f.hom (M.F x) = N.F (f.hom x) :=
  f.map_F' x

/-- A morphism of Dieudonné modules commutes with the Verschiebung. -/
@[simp]
theorem Hom.map_V (f : M ⟶ N) (x : M) : f.hom (M.V x) = N.V (f.hom x) :=
  f.map_V' x

/-- An isomorphism of Dieudonné modules from a `𝕎 k`-linear equivalence commuting with `F` and
`V`. -/
@[simps]
def isoMk (e : M ≃ₗ[𝕎 k] N) (hF : ∀ x, e (M.F x) = N.F (e x))
    (hV : ∀ x, e (M.V x) = N.V (e x)) : M ≅ N where
  hom := ⟨e.toLinearMap, hF, hV⟩
  inv := ⟨e.symm.toLinearMap,
    fun y ↦ e.injective (by simp [hF]), fun y ↦ e.injective (by simp [hV])⟩
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-! ### The image of the Frobenius and of the Verschiebung -/

/-- The `𝕎 k`-submodule `F M` generated by the image of the Frobenius is that image, because the
Frobenius of `𝕎 k` is surjective. -/
theorem span_range_F (M : DieudonneModule.{v} p k) :
    Submodule.span (𝕎 k) (Set.range M.F) = LinearMap.range M.F := by
  rw [← LinearMap.coe_range, Submodule.span_eq]

/-- The `𝕎 k`-submodule `V M` generated by the image of the Verschiebung is that image, because
the inverse of the Frobenius of `𝕎 k` is surjective. -/
theorem span_range_V (M : DieudonneModule.{v} p k) :
    Submodule.span (𝕎 k) (Set.range M.V) = LinearMap.range M.V := by
  rw [← LinearMap.coe_range, Submodule.span_eq]

/-! ### Dieudonné modules as modules over the Dieudonné ring -/

private lemma frobeniusEquiv_symm_frobenius (ξ : 𝕎 k) :
    (frobeniusEquiv p k).symm (frobenius ξ) = ξ :=
  (frobeniusEquiv p k).symm_apply_apply ξ

private lemma frobenius_frobeniusEquiv_symm (ξ : 𝕎 k) :
    frobenius ((frobeniusEquiv p k).symm ξ) = ξ :=
  (frobeniusEquiv p k).apply_symm_apply ξ

section ModuleDieudonneRing

variable (M : DieudonneModule.{v} p k)

/-- The action of the Dieudonné ring on a Dieudonné module, as a ring homomorphism to the
additive endomorphisms: `C ξ`, `F` and `V` act by `ξ • ·`, `M.F` and `M.V`. -/
def toEnd : DieudonneRing p k →+* Module.End ℤ M :=
  DieudonneRing.lift (Module.toModuleEnd ℤ M) M.F.toAddMonoidHom.toIntLinearMap
    M.V.toAddMonoidHom.toIntLinearMap
    (fun ξ ↦ LinearMap.ext fun x ↦ by simp)
    (fun ξ ↦ LinearMap.ext fun x ↦ by
      simp [-WittVector.frobeniusEquiv_symm_apply, frobeniusEquiv_symm_frobenius])
    (LinearMap.ext fun x ↦ by simp [← Nat.cast_smul_eq_nsmul (𝕎 k)])
    (LinearMap.ext fun x ↦ by simp [← Nat.cast_smul_eq_nsmul (𝕎 k)])

/-- A Dieudonné module is a left module over the Dieudonné ring, through
`TauCeti.DieudonneModule.toEnd`. -/
instance instModuleDieudonneRing : Module (DieudonneRing p k) M :=
  Module.compHom M M.toEnd

@[simp]
theorem toEnd_apply (a : DieudonneRing p k) (x : M) : M.toEnd a x = a • x :=
  rfl

/-- The scalar `C ξ` of the Dieudonné ring acts on a Dieudonné module by `ξ`. -/
@[simp]
theorem C_smul (ξ : 𝕎 k) (x : M) : DieudonneRing.C p k ξ • x = ξ • x := by
  simp [← toEnd_apply, toEnd]

/-- The generator `F` of the Dieudonné ring acts on a Dieudonné module by its Frobenius. -/
@[simp]
theorem F_smul (x : M) : DieudonneRing.F p k • x = M.F x := by
  simp [← toEnd_apply, toEnd]

/-- The generator `V` of the Dieudonné ring acts on a Dieudonné module by its Verschiebung. -/
@[simp]
theorem V_smul (x : M) : DieudonneRing.V p k • x = M.V x := by
  simp [← toEnd_apply, toEnd]

instance : IsScalarTower (𝕎 k) (DieudonneRing p k) M :=
  ⟨fun ξ a x ↦ by rw [DieudonneRing.smul_def, mul_smul, C_smul]⟩

/-- A morphism of Dieudonné modules is linear over the Dieudonné ring. -/
theorem Hom.map_smul {M N : DieudonneModule.{v} p k} (f : M ⟶ N) (a : DieudonneRing p k)
    (x : M) : f.hom (a • x) = a • f.hom x := by
  induction a using DieudonneRing.induction_on generalizing x with
  | hC ξ => simp
  | hF => simp
  | hV => simp
  | hadd a b ha hb => simp [add_smul, ha, hb]
  | hmul a b ha hb => simp [mul_smul, ha, hb]

end ModuleDieudonneRing

/-! ### Modules over the Dieudonné ring as Dieudonné modules -/

section OfModule

variable (p k) (N : Type v) [AddCommGroup N] [Module (DieudonneRing p k) N]

/-- A left module over the Dieudonné ring as a Dieudonné module: `ξ ∈ 𝕎 k` acts by `C ξ`, and the
Frobenius and the Verschiebung are the actions of the generators `F` and `V`. -/
def ofModule : DieudonneModule.{v} p k :=
  letI : Module (𝕎 k) N := Module.compHom N (DieudonneRing.C p k)
  { carrier := N
    isModule := this
    F :=
      { toFun x := DieudonneRing.F p k • x
        map_add' := smul_add _
        map_smul' ξ x := by
          -- `ξ` acts on `ofModule N` through `DieudonneRing.C`
          change DieudonneRing.F p k • DieudonneRing.C p k ξ • x =
            DieudonneRing.C p k (frobenius ξ) • DieudonneRing.F p k • x
          rw [← mul_smul, DieudonneRing.F_mul_C, mul_smul] }
    V :=
      { toFun x := DieudonneRing.V p k • x
        map_add' := smul_add _
        map_smul' ξ x := by
          -- `ξ` acts on `ofModule N` through `DieudonneRing.C`
          change DieudonneRing.V p k • DieudonneRing.C p k ξ • x =
            DieudonneRing.C p k ((frobeniusEquiv p k).symm ξ) • DieudonneRing.V p k • x
          rw [← mul_smul, ← mul_smul, ← DieudonneRing.V_mul_C_frobenius,
            frobenius_frobeniusEquiv_symm] }
    F_V x := by
      -- `ξ` acts on `ofModule N` through `DieudonneRing.C`
      change DieudonneRing.F p k • DieudonneRing.V p k • x = DieudonneRing.C p k p • x
      rw [← mul_smul, DieudonneRing.F_mul_V, map_natCast]
    V_F x := by
      -- `ξ` acts on `ofModule N` through `DieudonneRing.C`
      change DieudonneRing.V p k • DieudonneRing.F p k • x = DieudonneRing.C p k p • x
      rw [← mul_smul, DieudonneRing.V_mul_F, map_natCast] }

variable {p k N}

@[simp]
theorem ofModule_F (x : N) : (ofModule p k N).F x = DieudonneRing.F p k • x :=
  rfl

@[simp]
theorem ofModule_V (x : N) : (ofModule p k N).V x = DieudonneRing.V p k • x :=
  rfl

/-- On `TauCeti.DieudonneModule.ofModule N`, the action of the Dieudonné ring defined by its
Frobenius and Verschiebung is the given action on `N`. -/
theorem toEnd_ofModule :
    (ofModule p k N).toEnd = Module.toModuleEnd ℤ (S := DieudonneRing p k) N := by
  ext <;> simp [toEnd_apply] <;> rfl

end OfModule

/-! ### The equivalence with modules over the Dieudonné ring -/

variable (p k) in
/-- A Dieudonné module as a left module over the Dieudonné ring. -/
@[simps obj]
def toModuleCat : DieudonneModule.{v} p k ⥤ ModuleCat.{v} (DieudonneRing p k) where
  obj M := .of _ M
  map f := ModuleCat.ofHom
    { toFun := f.hom
      map_add' := map_add f.hom
      map_smul' := f.map_smul }

@[simp]
theorem toModuleCat_map_hom_apply (f : M ⟶ N) (x : M) :
    ((toModuleCat p k).map f).hom x = f.hom x :=
  rfl

variable (p k) in
/-- A left module over the Dieudonné ring as a Dieudonné module. -/
@[simps obj]
def fromModuleCat : ModuleCat.{v} (DieudonneRing p k) ⥤ DieudonneModule.{v} p k where
  obj N := ofModule p k N
  map f :=
    { hom :=
        { toFun := f.hom
          map_add' := map_add f.hom
          map_smul' ξ x := f.hom.map_smul (DieudonneRing.C p k ξ) x }
      map_F' x := f.hom.map_smul (DieudonneRing.F p k) x
      map_V' x := f.hom.map_smul (DieudonneRing.V p k) x }

@[simp]
theorem fromModuleCat_map_hom_apply {N N' : ModuleCat.{v} (DieudonneRing p k)} (f : N ⟶ N')
    (x : N) : ((fromModuleCat p k).map f).hom x = f.hom x :=
  rfl

/-- A Dieudonné module is the Dieudonné module of its module over the Dieudonné ring. -/
def unitIso (M : DieudonneModule.{v} p k) :
    M ≅ (fromModuleCat p k).obj ((toModuleCat p k).obj M) :=
  isoMk
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' ξ x := (C_smul M ξ x).symm
      left_inv _ := rfl
      right_inv _ := rfl }
    (fun x ↦ (F_smul M x).symm) (fun x ↦ (V_smul M x).symm)

/-- A module over the Dieudonné ring is the module of its Dieudonné module. -/
def counitIso (N : ModuleCat.{v} (DieudonneRing p k)) :
    (toModuleCat p k).obj ((fromModuleCat p k).obj N) ≅ N :=
  LinearEquiv.toModuleIso
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' a x := DFunLike.congr_fun (DFunLike.congr_fun
        (toEnd_ofModule (N := ↑N)) a) x
      left_inv _ := rfl
      right_inv _ := rfl }

variable (p k) in
/-- **Dieudonné modules are left modules over the Dieudonné ring**: the category of Dieudonné
modules over `k` is equivalent to the category of left `D_k`-modules. -/
@[simps functor inverse]
def equivModuleCat : DieudonneModule.{v} p k ≌ ModuleCat.{v} (DieudonneRing p k) where
  functor := toModuleCat p k
  inverse := fromModuleCat p k
  unitIso := NatIso.ofComponents unitIso fun _ ↦ rfl
  counitIso := NatIso.ofComponents counitIso fun _ ↦ rfl
  functor_unitIso_comp _ := rfl

end DieudonneModule

end TauCeti
