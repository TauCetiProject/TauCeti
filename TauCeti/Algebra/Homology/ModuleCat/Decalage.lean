/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Algebra.Homology.CochainComplex.NormalizedDecalage
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Regular.NatCast

/-!
# The principal décalage of a cochain complex of modules

Let `R` be a commutative ring, `f ∈ R`, and `C` a `ℤ`-graded cochain complex of `R`-modules. The
*divisibility submodule* `E_f(C)ⁿ ⊆ Cⁿ` consists of the `x` whose differential is divisible by `f`,
that is `f • y = d x` for some `y`. When multiplication by `f` is injective on every term of `C`,
the element `y` is unique, it is again in `E_f(C)ⁿ⁺¹`, and `x ↦ y` is an `R`-linear map `δ`,
the *divided differential*, with `δ ∘ δ = 0`. The resulting complex `E_f(C)` is the *principal
décalage* of `C`. Multiplication by `fⁿ` in degree `n` identifies it with the subcomplex
`η_f C ⊆ C[1/f]`, `(η_f C)ⁿ = {x ∈ fⁿ Cⁿ | d x ∈ fⁿ⁺¹ Cⁿ⁺¹}`; this file works with `E_f(C)` only,
which avoids the localization and treats negative degrees like positive ones.

A cocycle of `E_f(C)` is the same as a cocycle of `C`, and a cocycle `z` is a coboundary of
`E_f(C)` exactly when `f • z` is a coboundary of `C`. So sending the class of a cocycle of `C` to
its class in `E_f(C)` is a surjection `Hⁿ(C) ⟶ Hⁿ(E_f(C))` with kernel the `f`-torsion
`Hⁿ(C)[f]`, natural in `C`: décalage removes exactly the `f`-torsion of the cohomology, and it
preserves quasi-isomorphisms between complexes with `f`-torsion-free terms. This is the input
for deriving `E_f` and for the décalage functors `Lη_f` of integral `p`-adic Hodge theory, such as
`Lη_μ` over `A_inf`. For `f = p` a natural number, the underlying complex of abelian groups of
`E_p(C)` is the normalized décalage `CochainComplex.normalizedDecalage` of the underlying complex
of abelian groups of `C` (`CochainComplex.forget₂PrincipalDecalageIso`).

## Main definitions

* `CochainComplex.decalageSubmodule C f n`: the elements of `Cⁿ` whose differential is divisible
  by `f`.
* `CochainComplex.principalDecalageD`: the divided differential `δ`, with `f • δ x = d x`.
* `CochainComplex.principalDecalage C f hC`: the complex `E_f(C)`.
* `CochainComplex.principalDecalageMap`: the cochain map `E_f(C) ⟶ E_f(D)` restricting a cochain
  map `C ⟶ D`.
* `CochainComplex.principalDecalageCyclesIso`: the cocycles of `E_f(C)` are those of `C`.
* `CochainComplex.homologyToPrincipalDecalage`: the map `Hⁿ(C) ⟶ Hⁿ(E_f(C))`.
* `CochainComplex.homologyPrincipalDecalageEquiv`: `Hⁿ(C) ⧸ Hⁿ(C)[f] ≃ₗ[R] Hⁿ(E_f(C))`.
* `CochainComplex.forget₂PrincipalDecalageIso`: for `f = p` a natural number, `E_p(C)` and the
  normalized décalage have the same underlying complex of abelian groups.

## Main results

* `CochainComplex.smul_principalDecalageD`, `CochainComplex.principalDecalageD_eq_iff`: `δ x` is
  the unique `y` with `f • y = d x`.
* `CochainComplex.principalDecalageD_eq_zero_iff`: the cocycles of `E_f(C)` are those of `C`.
* `CochainComplex.exists_principalDecalage_d_eq_iff`: an element `z` is a coboundary of `E_f(C)`
  exactly when `f • z` is a coboundary of `C`.
* `CochainComplex.homologyToPrincipalDecalage_surjective`,
  `CochainComplex.ker_homologyToPrincipalDecalage`: `Hⁿ(C) ⟶ Hⁿ(E_f(C))` is surjective with
  kernel `Hⁿ(C)[f]`.
* `CochainComplex.homologyMap_comp_homologyToPrincipalDecalage`: its naturality.
* `CochainComplex.quasiIso_principalDecalageMap`: `E_f` preserves quasi-isomorphisms.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Publ. Math. IHÉS 128 (2018),
  arXiv:1602.03148, Definition 6.2, Remark 6.3 and Lemma 6.4.
-/

public section

open CategoryTheory

universe v u

namespace CochainComplex

variable {R : Type u} [CommRing R]

section Submodule

variable (C : CochainComplex (ModuleCat.{v} R) ℤ) (f : R)

/-- The elements of `C.X n` whose differential is divisible by `f`: the degree-`n` term of the
principal décalage `E_f(C)`. -/
def decalageSubmodule (n : ℤ) : Submodule R (C.X n) :=
  (LinearMap.range (LinearMap.lsmul R (C.X (n + 1)) f)).comap (C.d n (n + 1)).hom

@[simp]
lemma mem_decalageSubmodule_iff {n : ℤ} {x : C.X n} :
    x ∈ C.decalageSubmodule f n ↔ ∃ y, f • y = C.d n (n + 1) x := by
  simp [decalageSubmodule]

variable {C f} in
/-- An element whose differential is `f • y` lies in `E_f(C)`. -/
lemma mem_decalageSubmodule_of_smul_eq {n : ℤ} {x : C.X n} {y : C.X (n + 1)}
    (h : f • y = C.d n (n + 1) x) : x ∈ C.decalageSubmodule f n :=
  (C.mem_decalageSubmodule_iff f).2 ⟨y, h⟩

variable {C} in
/-- Every cocycle lies in `E_f(C)`. -/
lemma mem_decalageSubmodule_of_d_eq_zero {n : ℤ} {x : C.X n} (hx : C.d n (n + 1) x = 0) :
    x ∈ C.decalageSubmodule f n :=
  mem_decalageSubmodule_of_smul_eq (y := 0) (by rw [smul_zero, hx])

/-- For `f = 0`, `E_f(C)ⁿ` consists of the cocycles. -/
@[simp]
lemma decalageSubmodule_zero (n : ℤ) :
    C.decalageSubmodule 0 n = LinearMap.ker (C.d n (n + 1)).hom := by
  ext x
  simp [eq_comm]

/-- For a unit `f`, every element lies in `E_f(C)`. -/
lemma decalageSubmodule_eq_top_of_isUnit {f : R} (hf : IsUnit f) (n : ℤ) :
    C.decalageSubmodule f n = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦
    mem_decalageSubmodule_of_smul_eq (y := (↑hf.unit⁻¹ : R) • C.d n (n + 1) x) ?_
  rw [smul_smul, hf.mul_val_inv, one_smul]

@[simp]
lemma decalageSubmodule_one (n : ℤ) : C.decalageSubmodule 1 n = ⊤ :=
  C.decalageSubmodule_eq_top_of_isUnit isUnit_one n

end Submodule

variable {C : CochainComplex (ModuleCat.{v} R) ℤ} {f : R} (hC : ∀ n, IsSMulRegular (C.X n) f)

section DividedDifferential

/-- The map `x ↦ d x / f` on `E_f(C)ⁿ`, with values in `Cⁿ⁺¹`. -/
private noncomputable def divD (n : ℤ) : C.decalageSubmodule f n →ₗ[R] C.X (n + 1) :=
  (LinearEquiv.ofInjective (LinearMap.lsmul R (C.X (n + 1)) f) (hC (n + 1))).symm.toLinearMap ∘ₗ
    ((C.d n (n + 1)).hom ∘ₗ (C.decalageSubmodule f n).subtype).codRestrict _ fun x ↦ x.property

private lemma smul_divD (n : ℤ) (x : C.decalageSubmodule f n) :
    f • divD hC n x = C.d n (n + 1) x :=
  LinearEquiv.ofInjective_symm_apply (f := LinearMap.lsmul R (C.X (n + 1)) f)
    (h := hC (n + 1)) _

private lemma d_divD (n : ℤ) (x : C.decalageSubmodule f n) :
    C.d (n + 1) (n + 1 + 1) (divD hC n x) = 0 := by
  refine hC (n + 1 + 1) ?_
  beta_reduce
  rw [smul_zero, ← map_smul, smul_divD, HomologicalComplex.d_comp_d_apply]

/-- The divided differential `δ : E_f(C)ⁿ → E_f(C)ⁿ⁺¹`, `x ↦ d x / f`. -/
noncomputable def principalDecalageD (n : ℤ) :
    C.decalageSubmodule f n →ₗ[R] C.decalageSubmodule f (n + 1) :=
  (divD hC n).codRestrict _ fun x ↦ C.mem_decalageSubmodule_of_d_eq_zero f (d_divD hC n x)

/-- The divisibility equation `f • δ x = d x`. -/
lemma smul_principalDecalageD (n : ℤ) (x : C.decalageSubmodule f n) :
    f • (principalDecalageD hC n x : C.X (n + 1)) = C.d n (n + 1) x :=
  smul_divD hC n x

/-- `δ x` is the unique `y` with `f • y = d x`. -/
lemma principalDecalageD_eq_iff {n : ℤ} {x : C.decalageSubmodule f n} {y : C.X (n + 1)} :
    (principalDecalageD hC n x : C.X (n + 1)) = y ↔ f • y = C.d n (n + 1) x :=
  ⟨fun h ↦ h ▸ smul_principalDecalageD hC n x,
    fun h ↦ hC (n + 1) ((smul_principalDecalageD hC n x).trans h.symm)⟩

/-- The divided differential takes values in the cocycles of `C`. -/
@[simp]
lemma d_principalDecalageD (n : ℤ) (x : C.decalageSubmodule f n) :
    C.d (n + 1) (n + 1 + 1) (principalDecalageD hC n x) = 0 :=
  d_divD hC n x

/-- The divided differential squares to zero. -/
@[simp]
lemma principalDecalageD_comp_principalDecalageD (n : ℤ) :
    principalDecalageD hC (n + 1) ∘ₗ principalDecalageD hC n = 0 := by
  ext x
  exact (principalDecalageD_eq_iff hC).2 (by simp)

/-- An element of `E_f(C)` is killed by `δ` exactly when it is a cocycle of `C`. -/
@[simp]
lemma principalDecalageD_eq_zero_iff {n : ℤ} {x : C.decalageSubmodule f n} :
    principalDecalageD hC n x = 0 ↔ C.d n (n + 1) x = 0 := by
  rw [← Submodule.coe_eq_zero, principalDecalageD_eq_iff, smul_zero, eq_comm]

/-- The kernel of `δ` is the preimage of the cocycles of `C` under the inclusion `E_f(C)ⁿ ⊆ Cⁿ`. -/
lemma ker_principalDecalageD (n : ℤ) :
    LinearMap.ker (principalDecalageD hC n) =
      (LinearMap.ker (C.d n (n + 1)).hom).comap (C.decalageSubmodule f n).subtype := by
  ext x
  exact principalDecalageD_eq_zero_iff hC

/-- For `f = 1` the divided differential is the differential of `C`. -/
@[simp]
lemma coe_principalDecalageD_one (hC : ∀ n, IsSMulRegular (C.X n) (1 : R)) (n : ℤ)
    (x : C.decalageSubmodule 1 n) :
    (principalDecalageD hC n x : C.X (n + 1)) = C.d n (n + 1) x :=
  (principalDecalageD_eq_iff hC).2 (one_smul R _)

end DividedDifferential

section Complex

variable (C f) in
/-- The principal décalage `E_f(C)` of a cochain complex of `R`-modules on whose terms
multiplication by `f` is injective: the elements `x` with `d x` divisible by `f`, with
differential `x ↦ d x / f`. -/
noncomputable abbrev principalDecalage : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (C.decalageSubmodule f n))
    (fun n ↦ ModuleCat.ofHom (principalDecalageD hC n))
    (fun n ↦ by ext1; exact principalDecalageD_comp_principalDecalageD hC n)

lemma principalDecalage_d_apply (n : ℤ) (x : C.decalageSubmodule f n) :
    (C.principalDecalage f hC).d n (n + 1) x = principalDecalageD hC n x := by
  simp only [principalDecalage, CochainComplex.of_d, ModuleCat.hom_ofHom]

/-- The cocycles of `E_f(C)` are the elements of `E_f(C)` that are cocycles of `C`. -/
lemma principalDecalage_d_eq_zero_iff {n : ℤ} {x : C.decalageSubmodule f n} :
    (C.principalDecalage f hC).d n (n + 1) x = 0 ↔ C.d n (n + 1) x = 0 := by
  rw [principalDecalage_d_apply, principalDecalageD_eq_zero_iff]

/-- The differential of `E_f(C)` multiplied by `f` is the differential of `C`. -/
lemma smul_principalDecalage_d (i j : ℤ) (x : C.decalageSubmodule f i) :
    f • Subtype.val ((C.principalDecalage f hC).d i j x) = C.d i j x := by
  by_cases hij : i + 1 = j
  · subst hij
    rw [principalDecalage_d_apply, smul_principalDecalageD]
  · rw [(C.principalDecalage f hC).shape i j hij, C.shape i j hij]
    simp

/-- Multiplication by `f` is injective on every term of `E_f(C)`. -/
lemma isSMulRegular_principalDecalage (n : ℤ) :
    IsSMulRegular ((C.principalDecalage f hC).X n) f :=
  (hC n).of_injective (C.decalageSubmodule f n).subtype Subtype.val_injective

/-- An element `z` of `Cʲ` is the differential of an element of `E_f(C)ⁱ` exactly when `f • z` is
the differential of an element of `Cⁱ`. -/
lemma exists_principalDecalage_d_eq_iff {i j : ℤ} (hij : i + 1 = j) (z : C.X j) :
    (∃ y : C.decalageSubmodule f i, Subtype.val ((C.principalDecalage f hC).d i j y) = z) ↔
      ∃ y : C.X i, C.d i j y = f • z := by
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨y.val, by rw [← smul_principalDecalage_d hC, hy]⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  subst hij
  refine ⟨⟨y, mem_decalageSubmodule_of_smul_eq hy.symm⟩, hC (i + 1) ?_⟩
  beta_reduce
  rw [smul_principalDecalage_d hC, hy]

end Complex

section Map

variable {D : CochainComplex (ModuleCat.{v} R) ℤ} (hD : ∀ n, IsSMulRegular (D.X n) f)

variable (f) in
/-- A cochain map sends `E_f(C)` into `E_f(D)`. -/
lemma map_mem_decalageSubmodule (φ : C ⟶ D) {n : ℤ} {x : C.X n}
    (hx : x ∈ C.decalageSubmodule f n) : φ.f n x ∈ D.decalageSubmodule f n := by
  obtain ⟨y, hy⟩ := (C.mem_decalageSubmodule_iff f).1 hx
  exact mem_decalageSubmodule_of_smul_eq (y := φ.f (n + 1) y) (by
    rw [← map_smul, hy, HomologicalComplex.Hom.comm_apply])

/-- The degree-`n` component of `principalDecalageMap`. -/
private noncomputable def principalDecalageMapF (φ : C ⟶ D) (n : ℤ) :
    (C.principalDecalage f hC).X n ⟶ (D.principalDecalage f hD).X n :=
  ModuleCat.ofHom (((φ.f n).hom ∘ₗ (C.decalageSubmodule f n).subtype).codRestrict _
    fun x ↦ map_mem_decalageSubmodule f φ x.property)

private lemma principalDecalageMapF_apply (φ : C ⟶ D) (n : ℤ)
    (x : (C.principalDecalage f hC).X n) :
    Subtype.val (principalDecalageMapF hC hD φ n x) = φ.f n x.val :=
  rfl

/-- The cochain map `E_f(C) ⟶ E_f(D)` induced by a cochain map `φ : C ⟶ D`: it is `φ` on
elements. -/
noncomputable def principalDecalageMap (φ : C ⟶ D) :
    C.principalDecalage f hC ⟶ D.principalDecalage f hD :=
  CochainComplex.ofHom (principalDecalageMapF hC hD φ) fun n ↦ by
    ext x
    refine hD (n + 1) ?_
    beta_reduce
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, smul_principalDecalage_d,
      principalDecalageMapF_apply, principalDecalageMapF_apply, ← map_smul,
      smul_principalDecalage_d, HomologicalComplex.Hom.comm_apply]

@[simp]
lemma principalDecalageMap_f_apply (φ : C ⟶ D) (n : ℤ) (x : C.decalageSubmodule f n) :
    Subtype.val ((principalDecalageMap hC hD φ).f n x) = φ.f n x :=
  (rfl)

@[simp]
lemma principalDecalageMap_id : principalDecalageMap hC hC (𝟙 C) = 𝟙 _ := by
  ext n x
  rfl

@[simp]
lemma principalDecalageMap_comp {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (hK : ∀ n, IsSMulRegular (K.X n) f) (φ : C ⟶ D) (ψ : D ⟶ K) :
    principalDecalageMap hC hK (φ ≫ ψ) =
      principalDecalageMap hC hD φ ≫ principalDecalageMap hD hK ψ := by
  ext n x
  rfl

end Map

section Homology

variable (f) in
/-- A cocycle of `C`, as an element of `E_f(C)`. -/
private noncomputable def cyclesToDecalage (n : ℤ) : C.cycles n →ₗ[R] C.decalageSubmodule f n :=
  (C.iCycles n).hom.codRestrict _ fun z ↦
    C.mem_decalageSubmodule_of_d_eq_zero f (C.iCycles_d_apply n (n + 1) z)

private lemma d_cyclesToDecalage (n : ℤ) (z : C.cycles n) :
    (C.principalDecalage f hC).d n (n + 1) (cyclesToDecalage f n z) = 0 := by
  rw [principalDecalage_d_eq_zero_iff]
  exact C.iCycles_d_apply n (n + 1) z

variable (f) in
/-- The cocycles of the principal décalage `E_f(C)` are the cocycles of `C`: an element of
`E_f(C)ⁿ` is killed by `δ` exactly when it is killed by `d`. -/
noncomputable def principalDecalageCyclesIso (n : ℤ) :
    (C.principalDecalage f hC).cycles n ≅ C.cycles n where
  hom := C.liftCycles ((C.principalDecalage f hC).iCycles n ≫
      ModuleCat.ofHom (X := (C.principalDecalage f hC).X n) (Y := C.X n)
        (C.decalageSubmodule f n).subtype) (n + 1) (by simp) (by
    ext z
    exact (principalDecalage_d_eq_zero_iff hC).1
      ((C.principalDecalage f hC).moduleCat_d_iCycles_apply n (n + 1) z))
  inv := (C.principalDecalage f hC).liftCycles
    (ModuleCat.ofHom (X := C.cycles n) (Y := (C.principalDecalage f hC).X n)
      (cyclesToDecalage f n)) (n + 1) (by simp) (by
    ext z : 2
    exact d_cyclesToDecalage hC n z)
  hom_inv_id := by
    ext z : 2
    refine (C.principalDecalage f hC).moduleCat_iCycles_injective n (Subtype.ext ?_)
    exact (congrArg Subtype.val (ConcreteCategory.congr_hom
      ((C.principalDecalage f hC).liftCycles_i _ _ _ _) _)).trans
        (ConcreteCategory.congr_hom (C.liftCycles_i _ _ _ _) z)
  inv_hom_id := by
    ext z : 2
    refine C.moduleCat_iCycles_injective n ?_
    exact (ConcreteCategory.congr_hom (C.liftCycles_i _ _ _ _) _).trans
      (congrArg Subtype.val (ConcreteCategory.congr_hom
        ((C.principalDecalage f hC).liftCycles_i _ _ _ _) z))

/-- `principalDecalageCyclesIso` does not change the underlying element of a cocycle. -/
@[simp]
lemma iCycles_principalDecalageCyclesIso_hom_apply (n : ℤ)
    (z : (C.principalDecalage f hC).cycles n) :
    C.iCycles n ((C.principalDecalageCyclesIso f hC n).hom z) =
      Subtype.val ((C.principalDecalage f hC).iCycles n z) := by
  dsimp only [principalDecalageCyclesIso]
  exact ConcreteCategory.congr_hom (C.liftCycles_i _ _ _ _) z

/-- The inverse of `principalDecalageCyclesIso` does not change the underlying element of a
cocycle. -/
@[simp]
lemma iCycles_principalDecalageCyclesIso_inv_apply (n : ℤ) (z : C.cycles n) :
    Subtype.val ((C.principalDecalage f hC).iCycles n
      ((C.principalDecalageCyclesIso f hC n).inv z)) = C.iCycles n z := by
  dsimp only [principalDecalageCyclesIso]
  exact congrArg Subtype.val
    (ConcreteCategory.congr_hom ((C.principalDecalage f hC).liftCycles_i _ _ _ _) z)

/-- The class in `Hⁿ(E_f(C))` of a cocycle of `C`. -/
private noncomputable def cyclesToHomologyPrincipalDecalage (n : ℤ) :
    C.cycles n →ₗ[R] (C.principalDecalage f hC).homology n :=
  (C.principalDecalage f hC).moduleCatHomologyClass (CochainComplex.next ℤ n)
    (cyclesToDecalage f n) (d_cyclesToDecalage hC n)

/-- A cocycle `z` of `C` has zero class in `Hⁿ(E_f(C))` exactly when `f • z` is a coboundary
of `C`. -/
private lemma cyclesToHomologyPrincipalDecalage_eq_zero_iff {n : ℤ} (z : C.cycles n) :
    cyclesToHomologyPrincipalDecalage hC n z = 0 ↔
      ∃ y : C.X (n - 1), C.d (n - 1) n y = f • C.iCycles n z := by
  rw [cyclesToHomologyPrincipalDecalage, HomologicalComplex.moduleCatHomologyClass_eq_zero_iff _ _ _
    _ (CochainComplex.prev ℤ n), ← exists_principalDecalage_d_eq_iff hC (sub_add_cancel n 1)]
  exact exists_congr fun y ↦ Subtype.ext_iff

private lemma cyclesToHomologyPrincipalDecalage_surjective (n : ℤ) :
    Function.Surjective (cyclesToHomologyPrincipalDecalage hC n) :=
  HomologicalComplex.moduleCatHomologyClass_surjective _ _ _ _ fun x hx ↦
    ⟨C.moduleCatCyclesMk x.val (n + 1) (CochainComplex.next ℤ n)
      ((principalDecalage_d_eq_zero_iff hC).1 hx),
      Subtype.ext (C.iCycles_moduleCatCyclesMk _ _ _ _ _)⟩

variable (f) in
/-- The map `Hⁿ(C) ⟶ Hⁿ(E_f(C))` sending the class of a cocycle of `C` to its class as a cocycle
of the principal décalage `E_f(C)`. It is surjective, with kernel the `f`-torsion of `Hⁿ(C)`. -/
noncomputable def homologyToPrincipalDecalage (n : ℤ) :
    C.homology n ⟶ (C.principalDecalage f hC).homology n :=
  (C.homologyIsCokernel (n - 1) n (CochainComplex.prev ℤ n)).desc (Limits.CokernelCofork.ofπ
    (ModuleCat.ofHom (cyclesToHomologyPrincipalDecalage hC n)) (by
      ext y
      refine (cyclesToHomologyPrincipalDecalage_eq_zero_iff hC _).2 ⟨f • y, ?_⟩
      rw [map_smul]
      exact congrArg (f • ·) (C.moduleCat_iCycles_toCycles_apply n (n - 1) y).symm))

private lemma homologyToPrincipalDecalage_homologyπ (n : ℤ) (z : C.cycles n) :
    C.homologyToPrincipalDecalage f hC n (C.homologyπ n z) =
      cyclesToHomologyPrincipalDecalage hC n z := by
  rw [← ModuleCat.comp_apply]
  exact ConcreteCategory.congr_hom
    (Limits.Cofork.IsColimit.π_desc (C.homologyIsCokernel (n - 1) n (CochainComplex.prev ℤ n))) z

/-- `homologyToPrincipalDecalage` sends the class of a cocycle of `C` to the class of the same
cocycle of `E_f(C)`. -/
@[simp]
lemma homologyToPrincipalDecalage_homologyπ_apply (n : ℤ) (z : C.cycles n) :
    C.homologyToPrincipalDecalage f hC n (C.homologyπ n z) =
      (C.principalDecalage f hC).homologyπ n ((C.principalDecalageCyclesIso f hC n).inv z) := by
  rw [homologyToPrincipalDecalage_homologyπ, cyclesToHomologyPrincipalDecalage,
    HomologicalComplex.moduleCatHomologyClass_apply]
  congr 1
  refine (C.principalDecalage f hC).moduleCat_iCycles_injective n (Subtype.ext ?_)
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, iCycles_principalDecalageCyclesIso_inv_apply]
  rfl

/-- `homologyToPrincipalDecalage` sends the class of a cocycle of `C` to the class of the same
cocycle of `E_f(C)`. -/
@[reassoc (attr := simp)]
lemma homologyπ_homologyToPrincipalDecalage (n : ℤ) :
    C.homologyπ n ≫ C.homologyToPrincipalDecalage f hC n =
      (C.principalDecalageCyclesIso f hC n).inv ≫ (C.principalDecalage f hC).homologyπ n := by
  ext z : 2
  exact homologyToPrincipalDecalage_homologyπ_apply hC n z

/-- `homologyToPrincipalDecalage` sends the class of a cocycle of `C` lying in `E_f(C)` to its
class as a cocycle of `E_f(C)`. -/
lemma homologyToPrincipalDecalage_homologyπ_moduleCatCyclesMk {n : ℤ}
    (x : C.decalageSubmodule f n) (hx : (C.principalDecalage f hC).d n (n + 1) x = 0) :
    C.homologyToPrincipalDecalage f hC n (C.homologyπ n (C.moduleCatCyclesMk x.val (n + 1)
      (CochainComplex.next ℤ n)
        ((principalDecalage_d_eq_zero_iff hC).1 hx))) =
      (C.principalDecalage f hC).homologyπ n
        ((C.principalDecalage f hC).moduleCatCyclesMk x (n + 1) (CochainComplex.next ℤ n) hx) := by
  rw [homologyToPrincipalDecalage_homologyπ, cyclesToHomologyPrincipalDecalage,
    HomologicalComplex.moduleCatHomologyClass_apply]
  congr
  exact Subtype.ext (C.iCycles_moduleCatCyclesMk _ _ _ _ _)

/-- Every cohomology class of `E_f(C)` is the class of a cocycle of `C`. -/
lemma homologyToPrincipalDecalage_surjective (n : ℤ) :
    Function.Surjective (C.homologyToPrincipalDecalage f hC n) := by
  intro x
  obtain ⟨z, rfl⟩ := cyclesToHomologyPrincipalDecalage_surjective hC n x
  exact ⟨C.homologyπ n z, homologyToPrincipalDecalage_homologyπ hC n z⟩

/-- A class of `Hⁿ(C)` vanishes in `Hⁿ(E_f(C))` exactly when it is killed by `f`. -/
lemma homologyToPrincipalDecalage_apply_eq_zero_iff {n : ℤ} (x : C.homology n) :
    C.homologyToPrincipalDecalage f hC n x = 0 ↔ f • x = 0 := by
  obtain ⟨z, rfl⟩ := C.moduleCat_homologyπ_surjective n x
  rw [homologyToPrincipalDecalage_homologyπ, cyclesToHomologyPrincipalDecalage_eq_zero_iff]
  conv_rhs => rw [← map_smul, C.moduleCat_homologyπ_eq_zero_iff (CochainComplex.prev ℤ n)]
  refine exists_congr fun y ↦ ?_
  rw [← (C.moduleCat_iCycles_injective n).eq_iff, C.moduleCat_iCycles_toCycles_apply, map_smul]

/-- The kernel of `Hⁿ(C) ⟶ Hⁿ(E_f(C))` is the `f`-torsion submodule `Hⁿ(C)[f]`. -/
lemma ker_homologyToPrincipalDecalage (n : ℤ) :
    LinearMap.ker (C.homologyToPrincipalDecalage f hC n).hom =
      Submodule.torsionBy R (C.homology n) f := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_torsionBy_iff]
  exact homologyToPrincipalDecalage_apply_eq_zero_iff hC x

variable (f) in
/-- The cohomology of the principal décalage: `Hⁿ(C) ⧸ Hⁿ(C)[f] ≃ₗ[R] Hⁿ(E_f(C))`, induced by
sending a cocycle of `C` to its class as a cocycle of `E_f(C)`. -/
noncomputable def homologyPrincipalDecalageEquiv (n : ℤ) :
    (C.homology n ⧸ Submodule.torsionBy R (C.homology n) f) ≃ₗ[R]
      (C.principalDecalage f hC).homology n :=
  (Submodule.quotEquivOfEq _ _ (C.ker_homologyToPrincipalDecalage hC n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (C.homologyToPrincipalDecalage_surjective hC n))

/-- `homologyPrincipalDecalageEquiv` sends the class of `x` modulo `f`-torsion to the image of `x`
under `homologyToPrincipalDecalage`. -/
@[simp]
lemma homologyPrincipalDecalageEquiv_mk {n : ℤ} (x : C.homology n) :
    C.homologyPrincipalDecalageEquiv f hC n (Submodule.Quotient.mk x) =
      C.homologyToPrincipalDecalage f hC n x := by
  simp [homologyPrincipalDecalageEquiv, LinearMap.quotKerEquivOfSurjective]

section Naturality

variable {D : CochainComplex (ModuleCat.{v} R) ℤ} (hD : ∀ n, IsSMulRegular (D.X n) f)

/-- The map `Hⁿ(C) ⟶ Hⁿ(E_f(C))` is natural in `C`. -/
@[reassoc, elementwise]
lemma homologyMap_comp_homologyToPrincipalDecalage (φ : C ⟶ D) (n : ℤ) :
    HomologicalComplex.homologyMap φ n ≫ D.homologyToPrincipalDecalage f hD n =
      C.homologyToPrincipalDecalage f hC n ≫
        HomologicalComplex.homologyMap (principalDecalageMap hC hD φ) n := by
  have h (z : C.cycles n) : (principalDecalageMap hC hD φ).f n (cyclesToDecalage f n z) =
      cyclesToDecalage f n (HomologicalComplex.cyclesMap φ n z) :=
    Subtype.ext (C.moduleCat_iCycles_cyclesMap_apply n φ z).symm
  rw [← cancel_epi (C.homologyπ n), HomologicalComplex.homologyπ_naturality_assoc]
  ext z
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply,
    homologyToPrincipalDecalage_homologyπ, homologyToPrincipalDecalage_homologyπ,
    cyclesToHomologyPrincipalDecalage, cyclesToHomologyPrincipalDecalage,
    HomologicalComplex.homologyMap_moduleCatHomologyClass _ _ _ _ _ (d_cyclesToDecalage hD n) _ h]

/-- The principal décalage preserves quasi-isomorphisms in each degree. -/
instance quasiIsoAt_principalDecalageMap (φ : C ⟶ D) (n : ℤ) [QuasiIsoAt φ n] :
    QuasiIsoAt (principalDecalageMap hC hD φ) n := by
  have hφ := (ConcreteCategory.isIso_iff_bijective (HomologicalComplex.homologyMap φ n)).1
    ((quasiIsoAt_iff_isIso_homologyMap φ n).1 inferInstance)
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := C.homologyToPrincipalDecalage_surjective hC n x
    rw [← homologyMap_comp_homologyToPrincipalDecalage_apply,
      homologyToPrincipalDecalage_apply_eq_zero_iff, ← map_smul] at hx
    rw [homologyToPrincipalDecalage_apply_eq_zero_iff]
    exact hφ.1 (hx.trans (map_zero _).symm)
  · obtain ⟨y, rfl⟩ := D.homologyToPrincipalDecalage_surjective hD n y
    obtain ⟨x, rfl⟩ := hφ.2 y
    exact ⟨_, (homologyMap_comp_homologyToPrincipalDecalage_apply hC hD φ n x).symm⟩

/-- The principal décalage preserves quasi-isomorphisms. -/
instance quasiIso_principalDecalageMap (φ : C ⟶ D) [QuasiIso φ] :
    QuasiIso (principalDecalageMap hC hD φ) where
  quasiIsoAt _ := inferInstance

end Naturality

end Homology

section NatCast

variable {p : ℕ} (hC : ∀ n, IsSMulRegular (C.X n) (p : R))

variable (C p) in
/-- For a natural number `p`, the divisibility submodule `E_p(C)ⁿ` of `C` is the divisibility
subgroup of the underlying complex of abelian groups. -/
lemma toAddSubgroup_decalageSubmodule_natCast (n : ℤ) :
    (C.decalageSubmodule (p : R) n).toAddSubgroup =
      decalageAddSubgroup
        (((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex _).obj C) p n := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, mem_decalageSubmodule_iff, Nat.cast_smul_eq_nsmul]
  exact (mem_decalageAddSubgroup_iff
    (((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex _).obj C) p
    (x := x)).symm

/-- For a natural number `p`, the underlying complex of abelian groups of the principal décalage
`E_p(C)` is the normalized décalage of the underlying complex of abelian groups of `C`. Both are
`x ↦ d x / p` on the same elements. -/
noncomputable def forget₂PrincipalDecalageIso :
    ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex _).obj
        (C.principalDecalage (p : R) hC) ≅
      normalizedDecalage
        (((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex _).obj C) p
        fun n ↦ (TauCeti.isSMulRegular_natCast_iff (M := C.X n)).1 (hC n) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦
      (AddEquiv.addSubgroupCongr (C.toAddSubgroup_decalageSubmodule_natCast p n)).toAddCommGrpIso)
    (by
      rintro n _ rfl
      ext x
      refine (TauCeti.isSMulRegular_natCast_iff (M := C.X (n + 1))).1 (hC (n + 1)) ?_
      beta_reduce
      rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, smul_normalizedDecalage_d]
      exact ((Nat.cast_smul_eq_nsmul R p _).symm.trans
        (smul_principalDecalage_d hC n (n + 1) x)).symm)

/-- `forget₂PrincipalDecalageIso` does not change the underlying elements. -/
lemma forget₂PrincipalDecalageIso_hom_f_apply (n : ℤ) (x : C.decalageSubmodule (p : R) n) :
    Subtype.val (((forget₂PrincipalDecalageIso hC).hom.f n).hom x) = x.val :=
  (rfl)

/-- The inverse of `forget₂PrincipalDecalageIso` does not change the underlying elements. -/
lemma forget₂PrincipalDecalageIso_inv_f_apply (n : ℤ)
    (x : decalageAddSubgroup
      (((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex _).obj C) p n) :
    Subtype.val (((forget₂PrincipalDecalageIso hC).inv.f n).hom x) = x.val :=
  (rfl)

end NatCast

end CochainComplex
