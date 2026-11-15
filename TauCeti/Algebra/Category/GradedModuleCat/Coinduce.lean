/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian

/-!
# Coinduced graded modules and enough injectives

For a graded `k`-algebra `A` with homogeneous pieces `𝒜`, the forgetful functor
`TauCeti.GradedModuleCat.toModuleCat` from graded `𝒜`-modules to ungraded `A`-modules admits a
right adjoint `TauCeti.GradedModuleCat.coinduce`. Given an `A`-module `V`, the coinduced graded
module has a copy of `V` as its homogeneous piece in every degree `p : ℤ`, and a homogeneous
scalar `a ∈ 𝒜 q` sends the copy in degree `p` to the copy in degree `q + p` by `v ↦ a • v`.

For a graded module `M` and an ungraded module `V`, an `A`-linear map `f : M →ₗ[A] V` corresponds
under the adjunction to the degree-zero map sending each homogeneous component `mₚ ∈ Mₚ` to `f mₚ`
in the degree-`p` summand; the inverse correspondence sums the coordinates in `V`. Both directions
use that `M` and `A` are direct sums of their homogeneous pieces, so no finiteness or boundedness
assumption on the grading is needed.

Since `toModuleCat` preserves and reflects monomorphisms, `coinduce` preserves injective objects,
and Mathlib's `EnoughInjectives.of_adjunction` transfers enough injectives from `ModuleCat A` to
`GradedModuleCat 𝒜`.

## Main definitions

* `TauCeti.GradedModuleCat.coinduce`: the coinduction functor from `ModuleCat A` to
  `GradedModuleCat 𝒜`.
* `TauCeti.GradedModuleCat.toModuleCatAdjCoinduce`: the adjunction `toModuleCat ⊣ coinduce`.

## Main results

* `TauCeti.GradedModuleCat.enoughInjectives`: the category of graded `𝒜`-modules has enough
  injectives (and as an instance whenever `Small.{v} A`).

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, LNM **1836**, Springer (2004),
  Section 2.2 (Proposition 2.2.2) and Section 2.3.
-/

public section

open CategoryTheory
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe v uk uA

section Piece

/-- A copy of an `A`-module equipped with the base `k`-module structure induced by `Algebra k A`,
avoiding typeclass diamonds on `ModuleCat` carriers that do not carry a `Module k` instance. -/
@[ext]
private structure CoinducePiece (k : Type uk) (A : Type uA) (V : Type v) where
  val : V

section Group

variable {k : Type uk} {A : Type uA} {V : Type v} [AddCommGroup V]

private instance : Zero (CoinducePiece k A V) := ⟨⟨0⟩⟩
private instance : Add (CoinducePiece k A V) := ⟨fun x y ↦ ⟨x.val + y.val⟩⟩
private instance : Neg (CoinducePiece k A V) := ⟨fun x ↦ ⟨-x.val⟩⟩
private instance : Sub (CoinducePiece k A V) := ⟨fun x y ↦ ⟨x.val - y.val⟩⟩
private instance : SMul ℕ (CoinducePiece k A V) := ⟨fun n x ↦ ⟨n • x.val⟩⟩
private instance : SMul ℤ (CoinducePiece k A V) := ⟨fun n x ↦ ⟨n • x.val⟩⟩

private instance : AddCommGroup (CoinducePiece k A V) :=
  Function.Injective.addCommGroup CoinducePiece.val (fun _ _ ↦ CoinducePiece.ext)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp]
private theorem coinducePiece_zero_val : (0 : CoinducePiece k A V).val = 0 := rfl

@[simp]
private theorem coinducePiece_add_val (x y : CoinducePiece k A V) :
    (x + y).val = x.val + y.val := rfl

end Group

section Module

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {V : Type v} [AddCommGroup V] [Module A V]

private instance : SMul k (CoinducePiece k A V) where
  smul c x := ⟨algebraMap k A c • x.val⟩

@[simp]
private theorem coinducePiece_smul_val (c : k) (x : CoinducePiece k A V) :
    (c • x).val = algebraMap k A c • x.val := rfl

private instance : Module k (CoinducePiece k A V) where
  one_smul x := CoinducePiece.ext (by simp)
  mul_smul c d x := CoinducePiece.ext (by simp [mul_smul])
  smul_zero c := CoinducePiece.ext (by simp)
  smul_add c x y := CoinducePiece.ext (by simp [smul_add])
  add_smul c d x := CoinducePiece.ext (by simp [add_smul])
  zero_smul x := CoinducePiece.ext (by simp)

/-- Scalar action of `a : A` on `CoinducePiece k A V` as a `k`-linear endomorphism. -/
private def pieceAction : A →ₗ[k] Module.End k (CoinducePiece k A V) where
  toFun a :=
    { toFun x := ⟨a • x.val⟩
      map_add' x y := CoinducePiece.ext (smul_add a x.val y.val)
      map_smul' c x := CoinducePiece.ext (by
        simp only [coinducePiece_smul_val, RingHom.id_apply, ← mul_smul, Algebra.commutes]) }
  map_add' a b := by ext x; exact add_smul a b x.val
  map_smul' c a := by
    ext x
    simp [Algebra.smul_def, mul_smul]

@[simp]
private theorem pieceAction_apply_val (a : A) (x : CoinducePiece k A V) :
    (pieceAction (k := k) (A := A) (V := V) a x).val = a • x.val :=
  rfl

end Module

end Piece

section Coinduce

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A)

/-- Wrapper carrier for the coinduced graded module on `V`. -/
@[ext]
private structure CoinduceCarrier (𝒜 : ℤ → Submodule k A) (V : Type v) [AddCommGroup V] where
  raw : ⨁ _ : ℤ, CoinducePiece k A V

private instance (V : Type v) [AddCommGroup V] : Zero (CoinduceCarrier 𝒜 V) := ⟨⟨0⟩⟩
private instance (V : Type v) [AddCommGroup V] : Add (CoinduceCarrier 𝒜 V) :=
  ⟨fun x y ↦ ⟨x.raw + y.raw⟩⟩
private instance (V : Type v) [AddCommGroup V] : Neg (CoinduceCarrier 𝒜 V) := ⟨fun x ↦ ⟨-x.raw⟩⟩
private instance (V : Type v) [AddCommGroup V] : Sub (CoinduceCarrier 𝒜 V) :=
  ⟨fun x y ↦ ⟨x.raw - y.raw⟩⟩
private instance (V : Type v) [AddCommGroup V] : SMul ℕ (CoinduceCarrier 𝒜 V) :=
  ⟨fun n x ↦ ⟨n • x.raw⟩⟩
private instance (V : Type v) [AddCommGroup V] : SMul ℤ (CoinduceCarrier 𝒜 V) :=
  ⟨fun n x ↦ ⟨n • x.raw⟩⟩

private instance (V : Type v) [AddCommGroup V] : AddCommGroup (CoinduceCarrier 𝒜 V) :=
  Function.Injective.addCommGroup CoinduceCarrier.raw (fun _ _ ↦ CoinduceCarrier.ext)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

private instance (V : Type v) [AddCommGroup V] [Module A V] : SMul k (CoinduceCarrier 𝒜 V) where
  smul c g := ⟨c • g.raw⟩

private theorem coinduceCarrier_zero_raw {V : Type v} [AddCommGroup V] :
    (0 : CoinduceCarrier 𝒜 V).raw = 0 := rfl

private theorem coinduceCarrier_add_raw {V : Type v} [AddCommGroup V]
    (x y : CoinduceCarrier 𝒜 V) : (x + y).raw = x.raw + y.raw := rfl

private theorem coinduceCarrier_base_smul_raw {V : Type v} [AddCommGroup V] [Module A V]
    (c : k) (g : CoinduceCarrier 𝒜 V) : (c • g).raw = c • g.raw := rfl

private instance (V : Type v) [AddCommGroup V] [Module A V] : Module k (CoinduceCarrier 𝒜 V) :=
  Function.Injective.module k
    { toFun := CoinduceCarrier.raw, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    (fun _ _ ↦ CoinduceCarrier.ext) (fun _ _ ↦ rfl)

private def coinduceRawEquiv (V : Type v) [AddCommGroup V] [Module A V] :
    CoinduceCarrier 𝒜 V ≃ₗ[k] ⨁ _ : ℤ, CoinducePiece k A V where
  toFun := CoinduceCarrier.raw
  invFun g := ⟨g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def coinduceGrading (V : Type v) [AddCommGroup V] [Module A V] :
    InternalGrading k (CoinduceCarrier 𝒜 V) ℤ :=
  (InternalGrading.ofDecomposition
    (DirectSum.summand k fun _ : ℤ ↦ CoinducePiece k A V)).map (coinduceRawEquiv 𝒜 V).symm

private theorem mem_coinduceGrading_piece_iff {V : Type v} [AddCommGroup V] [Module A V]
    (p : ℤ) (g : CoinduceCarrier 𝒜 V) :
    g ∈ (coinduceGrading 𝒜 V).piece p ↔
      ∃ v : V, DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) p ⟨v⟩ = g.raw := by
  rw [coinduceGrading, InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
    InternalGrading.ofDecomposition_piece, DirectSum.mem_summand]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y.val, ?_⟩
    rwa [DirectSum.lof_eq_of]
  · rintro ⟨v, hv⟩
    refine ⟨⟨v⟩, ?_⟩
    rwa [← DirectSum.lof_eq_of k]

variable [GradedAlgebra 𝒜]

/-- A homogeneous scalar in `𝒜 q` sends the `p`-th summand of `⨁ _ : ℤ, CoinducePiece k A V` to
the `(q + p)`-th summand. -/
private noncomputable def coinduceHomogEnd (V : Type v) [AddCommGroup V] [Module A V] (q : ℤ) :
    𝒜 q →ₗ[k] Module.End k (⨁ _ : ℤ, CoinducePiece k A V) where
  toFun a := DirectSum.toModule k ℤ _ fun p ↦
    (DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) (q + p)).comp
      (pieceAction (k := k) (A := A) (V := V) (a : A))
  map_add' a b := by
    apply DirectSum.linearMap_ext k
    intro p
    apply LinearMap.ext
    intro x
    simp
  map_smul' c a := by
    apply DirectSum.linearMap_ext k
    intro p
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, map_smul,
      DirectSum.toModule_lof, RingHom.id_apply]

/-- The graded `A`-action on `⨁ _ : ℤ, CoinducePiece k A V`, assembled from homogeneous pieces of
`A` via `DirectSum.decomposeLinearEquiv`. -/
private noncomputable def coinduceActLinear (V : Type v) [AddCommGroup V] [Module A V] :
    A →ₗ[k] Module.End k (⨁ _ : ℤ, CoinducePiece k A V) :=
  (DirectSum.toModule k ℤ _ (coinduceHomogEnd 𝒜 V)).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

private theorem coinduceActLinear_of_mem {V : Type v} [AddCommGroup V] [Module A V]
    {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) (p : ℤ) (x : CoinducePiece k A V) :
    coinduceActLinear 𝒜 V a (DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) p x) =
      DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) (q + p) ⟨a • x.val⟩ := by
  dsimp only [coinduceActLinear]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_of_mem 𝒜 ha, ← DirectSum.lof_eq_of k ℤ (fun i ↦ 𝒜 i),
    DirectSum.toModule_lof]
  simp only [coinduceHomogEnd, LinearMap.coe_mk, AddHom.coe_mk, DirectSum.toModule_lof,
    LinearMap.comp_apply]
  rfl

private theorem coinduceActLinear_one (V : Type v) [AddCommGroup V] [Module A V] :
    coinduceActLinear 𝒜 V 1 = LinearMap.id := by
  apply DirectSum.linearMap_ext k
  intro p
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [coinduceActLinear_of_mem 𝒜 (SetLike.GradedOne.one_mem (A := 𝒜)) p x, zero_add, one_smul]

private theorem coinduceActLinear_mul (V : Type v) [AddCommGroup V] [Module A V] (a b : A) :
    coinduceActLinear 𝒜 V (a * b) =
      (coinduceActLinear 𝒜 V a).comp (coinduceActLinear 𝒜 V b) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a₁ a₂ ha₁ ha₂ => simp [add_mul, ha₁, ha₂, LinearMap.add_comp]
  | @homogeneous q₁ a =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add b₁ b₂ hb₁ hb₂ => simp [mul_add, hb₁, hb₂, LinearMap.comp_add]
    | @homogeneous q₂ b =>
      apply DirectSum.linearMap_ext k
      intro p
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply]
      have hab : (a : A) * (b : A) ∈ 𝒜 (q₁ + q₂) := SetLike.GradedMul.mul_mem a.2 b.2
      rw [coinduceActLinear_of_mem 𝒜 hab p x, coinduceActLinear_of_mem 𝒜 b.2 p x,
        coinduceActLinear_of_mem 𝒜 a.2 (q₂ + p) ⟨(b : A) • x.val⟩, add_assoc, mul_smul]

private noncomputable instance (V : Type v) [AddCommGroup V] [Module A V] :
    SMul A (CoinduceCarrier 𝒜 V) where
  smul a g := ⟨coinduceActLinear 𝒜 V a g.raw⟩

private theorem coinduceCarrier_smul_raw {V : Type v} [AddCommGroup V] [Module A V]
    (a : A) (g : CoinduceCarrier 𝒜 V) : (a • g).raw = coinduceActLinear 𝒜 V a g.raw := rfl

private noncomputable instance (V : Type v) [AddCommGroup V] [Module A V] :
    Module A (CoinduceCarrier 𝒜 V) where
  one_smul g := CoinduceCarrier.ext <| by
    rw [coinduceCarrier_smul_raw, coinduceActLinear_one, LinearMap.id_apply]
  mul_smul a b g := CoinduceCarrier.ext <| by
    rw [coinduceCarrier_smul_raw, coinduceCarrier_smul_raw, coinduceCarrier_smul_raw,
      coinduceActLinear_mul, LinearMap.comp_apply]
  smul_zero a := CoinduceCarrier.ext <| map_zero (coinduceActLinear 𝒜 V a)
  smul_add a g₁ g₂ := CoinduceCarrier.ext <| map_add (coinduceActLinear 𝒜 V a) g₁.raw g₂.raw
  add_smul a b g := CoinduceCarrier.ext <| by
    rw [coinduceCarrier_smul_raw, coinduceCarrier_add_raw, coinduceCarrier_smul_raw,
      coinduceCarrier_smul_raw, map_add, LinearMap.add_apply]
  zero_smul g := CoinduceCarrier.ext <| by
    rw [coinduceCarrier_smul_raw, coinduceCarrier_zero_raw, map_zero, LinearMap.zero_apply]

private instance (V : Type v) [AddCommGroup V] [Module A V] :
    IsScalarTower k A (CoinduceCarrier 𝒜 V) where
  smul_assoc c a g := CoinduceCarrier.ext <| by
    rw [coinduceCarrier_smul_raw, coinduceCarrier_base_smul_raw, coinduceCarrier_smul_raw,
      map_smul, LinearMap.smul_apply]

private noncomputable abbrev coinduceObj (V : ModuleCat.{v} A) : GradedModuleCat.{v} 𝒜 where
  carrier := CoinduceCarrier 𝒜 V
  grading := coinduceGrading 𝒜 V
  gradedSMul := ⟨fun {q p} a g ha hg ↦ by
    obtain ⟨v, hv⟩ := (mem_coinduceGrading_piece_iff 𝒜 p g).1 hg
    refine (mem_coinduceGrading_piece_iff 𝒜 (q + p) (a • g)).2 ⟨a • v, ?_⟩
    rw [coinduceCarrier_smul_raw, ← hv, coinduceActLinear_of_mem 𝒜 ha p ⟨v⟩]⟩

private noncomputable def coinduceMap {V W : ModuleCat.{v} A} (φ : V ⟶ W) :
    coinduceObj 𝒜 V ⟶ coinduceObj 𝒜 W := by
  let φk : CoinducePiece k A V →ₗ[k] CoinducePiece k A W :=
    { toFun x := ⟨φ.hom x.val⟩
      map_add' x y := CoinducePiece.ext (φ.hom.map_add x.val y.val)
      map_smul' c x := CoinducePiece.ext (φ.hom.map_smul (algebraMap k A c) x.val) }
  let L : (⨁ _ : ℤ, CoinducePiece k A V) →ₗ[k] (⨁ _ : ℤ, CoinducePiece k A W) :=
    DirectSum.lmap fun _ : ℤ ↦ φk
  let Lc : CoinduceCarrier 𝒜 V →ₗ[A] CoinduceCarrier 𝒜 W :=
    { toFun g := ⟨L g.raw⟩
      map_add' g₁ g₂ := CoinduceCarrier.ext (L.map_add g₁.raw g₂.raw)
      map_smul' a g := CoinduceCarrier.ext <| by
        dsimp only [RingHom.id_apply]
        rw [coinduceCarrier_smul_raw, coinduceCarrier_smul_raw]
        induction a using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp
        | add a₁ a₂ ha₁ ha₂ => simp [ha₁, ha₂]
        | @homogeneous q a =>
          have hcomp : L.comp (coinduceActLinear 𝒜 V a) =
              (coinduceActLinear 𝒜 W a).comp L := by
            apply DirectSum.linearMap_ext k
            intro p
            apply LinearMap.ext
            intro x
            simp only [LinearMap.comp_apply, L, DirectSum.lmap_lof,
              coinduceActLinear_of_mem 𝒜 a.2]
            congr 1
            exact CoinducePiece.ext (φ.hom.map_smul (a : A) x.val)
          exact LinearMap.congr_fun hcomp g.raw }
  exact ofHom Lc (LinearMap.isHomogeneous_def.2 fun p g hg ↦ by
    rw [add_zero]
    obtain ⟨v, hv⟩ := (mem_coinduceGrading_piece_iff 𝒜 p g).1 hg
    refine (mem_coinduceGrading_piece_iff 𝒜 p (Lc g)).2 ⟨φ.hom v, ?_⟩
    dsimp only [Lc, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hv, DirectSum.lmap_lof]
    rfl)

private theorem coinduceMap_apply_of_raw_eq {V W : ModuleCat.{v} A} (φ : V ⟶ W) {p : ℤ} {v : V}
    {g : CoinduceCarrier 𝒜 V}
    (hv : DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) p ⟨v⟩ = g.raw) :
    ((coinduceMap 𝒜 φ).hom g).raw =
      DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A W) p ⟨φ.hom v⟩ := by
  dsimp only [coinduceMap, hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hv, DirectSum.lmap_lof]
  rfl

/-- **Coinduction of modules to graded modules.** Right adjoint to `toModuleCat`: the homogeneous
piece of `(coinduce 𝒜).obj V` in every degree `p` is a copy of `V`, and homogeneous scalars shift
degrees while acting on `V`. -/
noncomputable def coinduce : ModuleCat.{v} A ⥤ GradedModuleCat.{v} 𝒜 where
  obj := coinduceObj 𝒜
  map := coinduceMap 𝒜
  map_id V := by
    apply hom_ext
    apply (coinduceGrading 𝒜 V).linearMap_ext
    intro p g hg
    obtain ⟨v, hv⟩ := (mem_coinduceGrading_piece_iff 𝒜 p g).1 hg
    apply CoinduceCarrier.ext
    rw [coinduceMap_apply_of_raw_eq 𝒜 (𝟙 V) hv]
    exact hv
  map_comp {U V W} φ ψ := by
    apply hom_ext
    apply (coinduceGrading 𝒜 U).linearMap_ext
    intro p g hg
    obtain ⟨u, hu⟩ := (mem_coinduceGrading_piece_iff 𝒜 p g).1 hg
    apply CoinduceCarrier.ext
    rw [coinduceMap_apply_of_raw_eq 𝒜 (φ ≫ ψ) hu, hom_comp, LinearMap.comp_apply,
      coinduceMap_apply_of_raw_eq 𝒜 ψ (coinduceMap_apply_of_raw_eq 𝒜 φ hu).symm]
    rfl

/-- For `f : M →ₗ[A] V`, the underlying `k`-linear map into `CoinducePiece k A V`. -/
private def toCoinducePieceLinear {M : GradedModuleCat.{v} 𝒜} {V : ModuleCat.{v} A}
    (f : M →ₗ[A] V) : M →ₗ[k] CoinducePiece k A V where
  toFun m := ⟨f m⟩
  map_add' m₁ m₂ := CoinducePiece.ext (f.map_add m₁ m₂)
  map_smul' c m := CoinducePiece.ext <| by
    simp only [coinducePiece_smul_val, RingHom.id_apply, ← f.map_smul,
      IsScalarTower.algebraMap_smul]

/-- The graded morphism `M ⟶ coinduceObj 𝒜 V` corresponding to an ungraded `A`-linear map
`M →ₗ[A] V`. -/
private noncomputable def homToCoinduce {M : GradedModuleCat.{v} 𝒜} {V : ModuleCat.{v} A}
    (f : M →ₗ[A] V) : M ⟶ coinduceObj 𝒜 V := by
  let fk := toCoinducePieceLinear (𝒜 := 𝒜) f
  let F : M →ₗ[k] ⨁ _ : ℤ, CoinducePiece k A V :=
    (DirectSum.lmap fun p : ℤ ↦ fk.comp (M.grading.piece p).subtype).comp
      (DirectSum.decomposeLinearEquiv M.grading.piece).toLinearMap
  have hF_mem {p : ℤ} {m : M} (hm : m ∈ M.grading.piece p) :
      F m = DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) p ⟨f m⟩ := by
    dsimp only [F]
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
      DirectSum.decompose_of_mem M.grading.piece hm,
      ← DirectSum.lof_eq_of k ℤ (fun i ↦ M.grading.piece i), DirectSum.lmap_lof]
    rfl
  let Fc : M →ₗ[A] CoinduceCarrier 𝒜 V :=
    { toFun m := ⟨F m⟩
      map_add' m₁ m₂ := CoinduceCarrier.ext (F.map_add m₁ m₂)
      map_smul' a m := CoinduceCarrier.ext <| by
        dsimp only [RingHom.id_apply]
        rw [coinduceCarrier_smul_raw]
        induction a using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp
        | add a₁ a₂ ha₁ ha₂ => simp [add_smul, ha₁, ha₂]
        | @homogeneous q a =>
          induction m using DirectSum.Decomposition.inductionOn M.grading.piece with
          | zero => simp
          | add m₁ m₂ hm₁ hm₂ => simp [smul_add, hm₁, hm₂]
          | @homogeneous p m =>
            have ham : (a : A) • (m : M) ∈ M.grading.piece (q + p) :=
              SetLike.GradedSMul.smul_mem a.2 m.2
            rw [hF_mem ham, hF_mem m.2, coinduceActLinear_of_mem 𝒜 a.2 p ⟨f (m : M)⟩,
              f.map_smul] }
  exact ofHom Fc (LinearMap.isHomogeneous_def.2 fun p m hm ↦ by
    rw [add_zero]
    exact (mem_coinduceGrading_piece_iff 𝒜 p (Fc m)).2 ⟨f m, (hF_mem hm).symm⟩)

private theorem homToCoinduce_apply_of_mem {M : GradedModuleCat.{v} 𝒜} {V : ModuleCat.{v} A}
    (f : M →ₗ[A] V) {p : ℤ} {m : M} (hm : m ∈ M.grading.piece p) :
    ((homToCoinduce 𝒜 f).hom m).raw =
      DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) p ⟨f m⟩ := by
  dsimp only [homToCoinduce, hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_of_mem M.grading.piece hm,
    ← DirectSum.lof_eq_of k ℤ (fun i ↦ M.grading.piece i), DirectSum.lmap_lof]
  rfl

/-- The counit map `coinduceObj 𝒜 V →ₗ[A] V` summing all homogeneous coordinates. -/
private noncomputable def coinduceCounitLinear (V : ModuleCat.{v} A) :
    CoinduceCarrier 𝒜 V →ₗ[A] V := by
  let S : (⨁ _ : ℤ, CoinducePiece k A V) →ₗ[k] CoinducePiece k A V :=
    DirectSum.toModule k ℤ (CoinducePiece k A V) fun _ : ℤ ↦ LinearMap.id
  exact
    { toFun g := (S g.raw).val
      map_add' g₁ g₂ := congrArg CoinducePiece.val (S.map_add g₁.raw g₂.raw)
      map_smul' a g := by
        simp only [RingHom.id_apply, coinduceCarrier_smul_raw]
        induction a using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp
        | add a₁ a₂ ha₁ ha₂ =>
          rw [map_add (coinduceActLinear 𝒜 V), LinearMap.add_apply, map_add, coinducePiece_add_val,
            ha₁, ha₂, add_smul]
        | @homogeneous q a =>
          have hS : S.comp (coinduceActLinear 𝒜 V a) =
              (pieceAction (k := k) (A := A) (V := V) (a : A)).comp S := by
            apply DirectSum.linearMap_ext k
            intro p
            apply LinearMap.ext
            intro x
            simp only [LinearMap.comp_apply, S, coinduceActLinear_of_mem 𝒜 a.2,
              DirectSum.toModule_lof, LinearMap.id_apply]
            rfl
          exact congrArg CoinducePiece.val (LinearMap.congr_fun hS g.raw) }

private theorem coinduceCounitLinear_of_raw_eq {V : ModuleCat.{v} A} {p : ℤ} {v : V}
    {g : CoinduceCarrier 𝒜 V}
    (hv : DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) p ⟨v⟩ = g.raw) :
    coinduceCounitLinear 𝒜 V g = v := by
  dsimp only [coinduceCounitLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hv, DirectSum.toModule_lof]
  rfl

private noncomputable def homFromCoinduce {M : GradedModuleCat.{v} 𝒜} {V : ModuleCat.{v} A}
    (g : M ⟶ (coinduce 𝒜).obj V) : M →ₗ[A] V :=
  (coinduceCounitLinear 𝒜 V).comp g.hom

/-- **The forgetful–coinduction adjunction** `toModuleCat ⊣ coinduce`. -/
noncomputable def toModuleCatAdjCoinduce :
    toModuleCat.{v} (𝒜 := 𝒜) ⊣ coinduce 𝒜 :=
  Adjunction.mkOfHomEquiv
    { homEquiv M V :=
        { toFun f := homToCoinduce 𝒜 f.hom
          invFun g := ModuleCat.ofHom (homFromCoinduce 𝒜 g)
          left_inv f := by
            apply ModuleCat.hom_ext
            apply M.grading.linearMap_ext
            intro p m hm
            rw [ModuleCat.hom_ofHom]
            exact coinduceCounitLinear_of_raw_eq 𝒜
              (homToCoinduce_apply_of_mem 𝒜 f.hom hm).symm
          right_inv g := by
            apply hom_ext
            apply M.grading.linearMap_ext
            intro p m hm
            apply CoinduceCarrier.ext
            obtain ⟨v, hv⟩ :=
              (mem_coinduceGrading_piece_iff 𝒜 p (g.hom m)).1 (GradedModuleCat.map_mem g hm)
            have hval : coinduceCounitLinear 𝒜 V (g.hom m) = v :=
              coinduceCounitLinear_of_raw_eq 𝒜 hv
            -- Beta-reduce `homEquiv` and identify `(ModuleCat.ofHom _).hom` across `ModuleCat.of`.
            change ((homToCoinduce 𝒜 (homFromCoinduce 𝒜 g)).hom m).raw = (g.hom m).raw
            exact (homToCoinduce_apply_of_mem 𝒜 (homFromCoinduce 𝒜 g) hm).trans
              ((congrArg (fun x ↦ DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducePiece k A V) p ⟨x⟩)
                hval).trans hv) }
      homEquiv_naturality_left_symm {M' M V} h g := by
        ext m
        rfl
      homEquiv_naturality_right {M V W} f ψ := by
        apply hom_ext
        apply M.grading.linearMap_ext
        intro p m hm
        apply CoinduceCarrier.ext
        -- Beta-reduce `homEquiv` and unfold `(coinduce 𝒜).map`.
        change ((homToCoinduce 𝒜 (f ≫ ψ).hom).hom m).raw =
          ((coinduceMap 𝒜 ψ).hom ((homToCoinduce 𝒜 f.hom).hom m)).raw
        rw [coinduceMap_apply_of_raw_eq 𝒜 ψ (homToCoinduce_apply_of_mem 𝒜 f.hom hm).symm,
          homToCoinduce_apply_of_mem 𝒜 (f ≫ ψ).hom hm]
        rfl }

/-- Coinduction preserves injective objects. -/
instance coinduce_preservesInjectiveObjects : (coinduce.{v} 𝒜).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (toModuleCatAdjCoinduce 𝒜)

/-- Every category of graded modules over a graded algebra has enough injectives in any universe
capable of holding the algebra. -/
instance enoughInjectives : EnoughInjectives (GradedModuleCat.{max uA v} 𝒜) :=
  letI := ModuleCat.enoughInjectives.{v, uA} A
  EnoughInjectives.of_adjunction (toModuleCatAdjCoinduce.{max uA v} 𝒜)

/-- When `A` is `v`-small, the category of `v`-small graded `𝒜`-modules has enough injectives. -/
instance enoughInjectivesOfSmall [Small.{v} A] : EnoughInjectives (GradedModuleCat.{v} 𝒜) :=
  EnoughInjectives.of_adjunction (toModuleCatAdjCoinduce.{v} 𝒜)

end Coinduce

end TauCeti.GradedModuleCat
