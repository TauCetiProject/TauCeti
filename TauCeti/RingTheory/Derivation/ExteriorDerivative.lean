/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.MapSemilinear
public import TauCeti.LinearAlgebra.ExteriorPower.Noetherian
import TauCeti.LinearAlgebra.ExteriorAlgebra.GradeInvolution

/-!
# Exterior derivative associated to a universal derivation

Let `D : Derivation R A M` be an `R`-derivation whose image spans `M` over `A`. Whenever the
twisted `A`-module `TwistedExt D = M × ⋀[A]^2 M` with `a • (m, ω) = (a • m, D a ∧ m + a • ω)`
receives an `A`-linear lift of `derTwistedExt D`, its second component extends uniquely to a
square-zero degree-`+1` graded `R`-derivation on `ExteriorAlgebra A M`, with no bases, smoothness,
or characteristic hypotheses.
-/

public section
namespace Derivation

/-- **The twisted extension `M × ⋀[A]^2 M` associated to a derivation `D : Derivation R A M`.**
As an abelian group it is `M × ⋀[A]^2 M`, with `a • (m, ω) = (a • m, D a ∧ m + a • ω)`. When the
image of `D` spans `M` over `A`, an `A`-linear map `u : M →ₗ[A] TwistedExt D` satisfying
`u (D a) = (D a, 0)` for all `a` is automatically a section of `fstLinear D` and determines a
unique square-zero degree-`+1` graded `R`-derivation on `ExteriorAlgebra A M` extending `D` (with
degree-`1` component `m ↦ (u m).snd`). -/
@[ext]
structure TwistedExt {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] (_D : Derivation R A M) where
  /-- The `M`-component of an element of `TwistedExt D`. -/
  fst : M
  /-- The `⋀[A]^2 M`-component of an element of `TwistedExt D`. -/
  snd : ⋀[A]^2 M
namespace TwistedExt
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] {D : Derivation R A M}
instance : Zero (TwistedExt D) := ⟨⟨0, 0⟩⟩
instance : Add (TwistedExt D) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (TwistedExt D) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
instance : Sub (TwistedExt D) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance : SMul ℕ (TwistedExt D) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
instance : SMul ℤ (TwistedExt D) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
instance : AddCommGroup (TwistedExt D) :=
  Function.Injective.addCommGroup (fun x : TwistedExt D ↦ (x.fst, x.snd))
    (fun _ _ h ↦ TwistedExt.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2) rfl (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
@[simp] theorem fst_zero : (0 : TwistedExt D).fst = 0 := (rfl)
@[simp] theorem snd_zero : (0 : TwistedExt D).snd = 0 := (rfl)
@[simp] theorem fst_add (x y : TwistedExt D) : (x + y).fst = x.fst + y.fst := (rfl)
@[simp] theorem snd_add (x y : TwistedExt D) : (x + y).snd = x.snd + y.snd := (rfl)
@[simp] theorem fst_neg (x : TwistedExt D) : (-x).fst = -x.fst := (rfl)
@[simp] theorem snd_neg (x : TwistedExt D) : (-x).snd = -x.snd := (rfl)
@[simp] theorem fst_sub (x y : TwistedExt D) : (x - y).fst = x.fst - y.fst := (rfl)
@[simp] theorem snd_sub (x y : TwistedExt D) : (x - y).snd = x.snd - y.snd := (rfl)

noncomputable instance : SMul A (TwistedExt D) :=
  ⟨fun a x ↦ ⟨a • x.fst, exteriorPower.ιMulti A 2 ![D a, x.fst] + a • x.snd⟩⟩
@[simp] theorem fst_smul (a : A) (x : TwistedExt D) : (a • x).fst = a • x.fst := (rfl)
@[simp] theorem snd_smul (a : A) (x : TwistedExt D) :
    (a • x).snd = exteriorPower.ιMulti A 2 ![D a, x.fst] + a • x.snd := (rfl)

noncomputable instance : Module A (TwistedExt D) where
  one_smul x := TwistedExt.ext (one_smul A x.fst) <| Subtype.ext <| by simp
  mul_smul a b x := TwistedExt.ext (mul_smul a b x.fst) <| Subtype.ext <| by
    simp only [snd_smul, fst_smul, Submodule.coe_add, SetLike.val_smul,
      exteriorPower.coe_ιMulti_two, D.leibniz, map_add, LinearMap.map_smul, add_mul,
      smul_mul_assoc, mul_smul_comm, smul_add, mul_smul]; abel
  smul_zero a := TwistedExt.ext (smul_zero a) <| Subtype.ext <| by simp
  smul_add a x y := TwistedExt.ext (smul_add a x.fst y.fst) <| Subtype.ext <| by
    simp only [snd_smul, fst_add, snd_add, Submodule.coe_add, SetLike.val_smul,
      exteriorPower.coe_ιMulti_two, map_add, mul_add, smul_add]; abel
  add_smul a b x := TwistedExt.ext (add_smul a b x.fst) <| Subtype.ext <| by
    simp only [snd_smul, snd_add, Submodule.coe_add, SetLike.val_smul,
      exteriorPower.coe_ιMulti_two, map_add, add_mul, add_smul]; abel
  zero_smul x := TwistedExt.ext (zero_smul A x.fst) <| Subtype.ext <| by simp

/-- The `A`-linear inclusion `⋀[A]^2 M →ₗ[A] TwistedExt D`, `ω ↦ (0, ω)`. -/
noncomputable def inl (D : Derivation R A M) : ⋀[A]^2 M →ₗ[A] TwistedExt D where
  toFun ω := ⟨0, ω⟩
  map_add' _ _ := TwistedExt.ext (by simp) rfl
  map_smul' _ _ := TwistedExt.ext (by simp) <| Subtype.ext <| by simp
/-- The `A`-linear first projection `TwistedExt D →ₗ[A] M`. -/
def fstLinear (D : Derivation R A M) : TwistedExt D →ₗ[A] M where
  toFun := fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem fst_inl (D : Derivation R A M) (ω : ⋀[A]^2 M) : (inl D ω).fst = 0 := (rfl)
@[simp] theorem snd_inl (D : Derivation R A M) (ω : ⋀[A]^2 M) : (inl D ω).snd = ω := (rfl)
@[simp] theorem fstLinear_apply (x : TwistedExt D) : fstLinear D x = x.fst := (rfl)

private theorem range_inl_eq_ker_fstLinear (D : Derivation R A M) :
    LinearMap.range (inl D) = LinearMap.ker (fstLinear D) :=
  Submodule.ext fun x ↦ ⟨by rintro ⟨ω, rfl⟩; rfl, fun hx ↦ ⟨x.snd, TwistedExt.ext hx.symm rfl⟩⟩

/-- `TwistedExt D` is a finite `A`-module whenever `M` is. -/
instance [Module.Finite A M] : Module.Finite A (TwistedExt D) :=
  Module.Finite.of_exact (LinearMap.exact_iff.mpr (range_inl_eq_ker_fstLinear D).symm)
    fun m ↦ ⟨⟨m, 0⟩, rfl⟩
/-- `TwistedExt D` is a Noetherian `A`-module whenever `M` is, without assuming `A` Noetherian. -/
instance [IsNoetherian A M] : IsNoetherian A (TwistedExt D) :=
  isNoetherian_of_range_eq_ker (inl D) (fstLinear D) (range_inl_eq_ker_fstLinear D)

variable [IsScalarTower R A M]
noncomputable instance : Module R (TwistedExt D) := Module.compHom (TwistedExt D) (algebraMap R A)
instance : IsScalarTower R A (TwistedExt D) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
@[simp] theorem fst_smul_base (r : R) (x : TwistedExt D) : (r • x).fst = r • x.fst :=
  algebraMap_smul A r x.fst
@[simp] theorem snd_smul_base (r : R) (x : TwistedExt D) : (r • x).snd = r • x.snd :=
  Subtype.ext <| by rw [← algebraMap_smul A r x, snd_smul]; simp [algebraMap_smul]
end TwistedExt
section TwistedAlg
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]
@[ext] private structure TwistedAlg (_D : Derivation R A M) where
  fst : ExteriorAlgebra A M
  snd : ExteriorAlgebra A M
namespace TwistedAlg
variable {D : Derivation R A M}
private instance : Zero (TwistedAlg D) := ⟨⟨0, 0⟩⟩
private instance : One (TwistedAlg D) := ⟨⟨1, 0⟩⟩
private instance : Add (TwistedAlg D) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private instance : Neg (TwistedAlg D) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
private instance : Sub (TwistedAlg D) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
private instance : SMul ℕ (TwistedAlg D) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
private instance : SMul ℤ (TwistedAlg D) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
private instance : AddCommGroup (TwistedAlg D) :=
  Function.Injective.addCommGroup (fun x : TwistedAlg D ↦ (x.fst, x.snd))
    (fun _ _ h ↦ TwistedAlg.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2) rfl (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
private noncomputable instance : Mul (TwistedAlg D) :=
  ⟨fun x y ↦ ⟨x.fst * y.fst,
    x.snd * y.fst + CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x.fst * y.snd⟩⟩
@[simp] private theorem fst_zero : (0 : TwistedAlg D).fst = 0 := (rfl)
@[simp] private theorem snd_zero : (0 : TwistedAlg D).snd = 0 := (rfl)
@[simp] private theorem fst_one : (1 : TwistedAlg D).fst = 1 := (rfl)
@[simp] private theorem snd_one : (1 : TwistedAlg D).snd = 0 := (rfl)
@[simp] private theorem fst_add (x y : TwistedAlg D) : (x + y).fst = x.fst + y.fst := (rfl)
@[simp] private theorem snd_add (x y : TwistedAlg D) : (x + y).snd = x.snd + y.snd := (rfl)
@[simp] private theorem fst_mul (x y : TwistedAlg D) : (x * y).fst = x.fst * y.fst := (rfl)
@[simp] private theorem snd_mul (x y : TwistedAlg D) :
    (x * y).snd = x.snd * y.fst +
      CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x.fst * y.snd := (rfl)

private noncomputable instance : Ring (TwistedAlg D) where
  __ := (inferInstance : AddCommGroup (TwistedAlg D))
  mul_assoc _ _ _ := TwistedAlg.ext (mul_assoc ..) <| by
    simp only [snd_mul, fst_mul, map_mul, add_mul, mul_add, mul_assoc]; abel
  one_mul _ := TwistedAlg.ext (one_mul _) (by simp)
  mul_one _ := TwistedAlg.ext (mul_one _) (by simp)
  zero_mul _ := TwistedAlg.ext (zero_mul _) (by simp)
  mul_zero _ := TwistedAlg.ext (mul_zero _) (by simp)
  left_distrib _ _ _ := TwistedAlg.ext (mul_add ..) <| by
    simp only [snd_mul, fst_add, snd_add, mul_add]; abel
  right_distrib _ _ _ := TwistedAlg.ext (add_mul ..) <| by
    simp only [snd_mul, fst_add, snd_add, map_add, add_mul]; abel

private noncomputable instance : Algebra A (TwistedAlg D) :=
  RingHom.toAlgebra'
    { toFun := fun a ↦ ⟨algebraMap A _ a, ExteriorAlgebra.ι A (D a)⟩
      map_one' := TwistedAlg.ext (map_one _) (by simp)
      map_mul' := fun a b ↦ TwistedAlg.ext (map_mul _ a b) <| by
        simp only [snd_mul, D.leibniz, map_add, LinearMap.map_smul,
          CliffordAlgebra.involute.commutes, ← Algebra.smul_def]
        rw [← Algebra.commutes b (ExteriorAlgebra.ι A (D a)), ← Algebra.smul_def, add_comm]
      map_zero' := TwistedAlg.ext (map_zero _) (by simp)
      map_add' := fun a b ↦ TwistedAlg.ext (map_add _ a b) (by simp) }
    fun a x ↦ TwistedAlg.ext (Algebra.commutes a x.fst) <| by
      simp only [snd_mul, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        CliffordAlgebra.involute.commutes, Algebra.commutes a x.snd,
        ExteriorAlgebra.ι_mul_eq_involute_mul, add_comm]

@[simp] private theorem fst_algebraMap (a : A) :
    (algebraMap A (TwistedAlg D) a).fst = algebraMap A (ExteriorAlgebra A M) a := (rfl)
@[simp] private theorem snd_algebraMap (a : A) :
    (algebraMap A (TwistedAlg D) a).snd = ExteriorAlgebra.ι A (D a) := (rfl)
end TwistedAlg
end TwistedAlg
/-! ### Construction of the graded exterior derivative -/
section ExteriorDeriv
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- **The canonical `R`-derivation `A → TwistedExt D`**, sending `a` to `(D a, 0)`. -/
noncomputable def derTwistedExt (D : Derivation R A M) : Derivation R A (TwistedExt D) where
  toFun a := ⟨D a, 0⟩
  map_add' _ _ := TwistedExt.ext (by simp) (by simp)
  map_smul' _ _ := TwistedExt.ext (by simp) (by simp)
  map_one_eq_zero' := TwistedExt.ext (by simp) rfl
  leibniz' _ _ := TwistedExt.ext (by simp [D.leibniz]) <| Subtype.ext <| by
    simp [ExteriorAlgebra.ι_add_mul_swap]
@[simp] theorem fst_derTwistedExt (D : Derivation R A M) (a : A) :
    (D.derTwistedExt a).fst = D a := (rfl)
@[simp] theorem snd_derTwistedExt (D : Derivation R A M) (a : A) :
    (D.derTwistedExt a).snd = 0 := (rfl)

omit [IsScalarTower R A M] in
private theorem eq_zero_of_gradedDeriv {B N : Type*} [CommRing B] [AddCommGroup N] [Module B N]
    (D : Derivation R A M) (hspan : Submodule.span A (Set.range D) = ⊤)
    (Φ Ψ : ExteriorAlgebra A M → ExteriorAlgebra B N)
    (Δ : ExteriorAlgebra A M →+ ExteriorAlgebra B N)
    (hmul : ∀ x y, Δ (x * y) = Δ x * Φ y + Ψ x * Δ y)
    (halg : ∀ a, Δ (algebraMap A _ a) = 0) (hD : ∀ a, Δ (ExteriorAlgebra.ι A (D a)) = 0)
    (x : ExteriorAlgebra A M) : Δ x = 0 := by
  have hι (m : M) : Δ (ExteriorAlgebra.ι A m) = 0 := by
    have hm : m ∈ Submodule.span A (Set.range D) := hspan ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem _ hm => obtain ⟨a, rfl⟩ := hm; exact hD a
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => simp [ih₁, ih₂]
    | smul a y _ ih => rw [LinearMap.map_smul, Algebra.smul_def, hmul, halg, ih]; simp
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => exact halg a
  | ι m => exact hι m
  | mul _ _ hx hy => rw [hmul, hx, hy]; simp
  | add _ _ hx hy => simp [hx, hy]

variable (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
  (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
include hspan hu in
private theorem fst_lift_eq_id (m : M) : (u m).fst = m := DFunLike.congr_fun
  (LinearMap.ext_on_range hspan fun a ↦ congrArg TwistedExt.fst (hu a) :
    TwistedExt.fstLinear D ∘ₗ u = LinearMap.id) m

include hspan hu in
private noncomputable def twistedLift : ExteriorAlgebra A M →ₐ[A] TwistedAlg D :=
  let L : M →ₗ[A] TwistedAlg D :=
    { toFun := fun m ↦ ⟨ExteriorAlgebra.ι A m, ((u m).snd : ExteriorAlgebra A M)⟩
      map_add' := fun m₁ m₂ ↦ TwistedAlg.ext (map_add _ m₁ m₂) (by simp [u.map_add])
      map_smul' := fun a m ↦ TwistedAlg.ext (by simp [Algebra.smul_def]) <| by
        rw [RingHom.id_apply, Algebra.smul_def, u.map_smul, TwistedExt.snd_smul,
          fst_lift_eq_id D u hspan hu m, Submodule.coe_add, SetLike.val_smul,
          exteriorPower.coe_ιMulti_two, TwistedAlg.snd_mul, TwistedAlg.snd_algebraMap,
          TwistedAlg.fst_algebraMap, CliffordAlgebra.involute.commutes, ← Algebra.smul_def] }
  ExteriorAlgebra.lift A ⟨L, fun m ↦ TwistedAlg.ext (ExteriorAlgebra.ι_sq_zero m) <| by
    rw [TwistedAlg.snd_mul, TwistedAlg.snd_zero]; dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    rw [CliffordAlgebra.involute_ι, neg_mul,
      ExteriorAlgebra.ι_mul_eq_involute_mul m ((u m).snd : ExteriorAlgebra A M),
      TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower (u m).snd.property]; simp⟩

private theorem fst_twistedLift (x : ExteriorAlgebra A M) :
    (twistedLift D u hspan hu x).fst = x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => exact congrArg TwistedAlg.fst ((twistedLift D u hspan hu).commutes a)
  | ι m => exact congrArg TwistedAlg.fst (ExteriorAlgebra.lift_ι_apply A _ _ m)
  | mul _ _ hx hy => rw [map_mul]; exact congrArg₂ (· * ·) hx hy
  | add _ _ hx hy => rw [map_add]; exact congrArg₂ (· + ·) hx hy

include D u hspan hu in
/-- **The graded exterior derivative on `ExteriorAlgebra A M`** associated to `D` and an
`A`-linear lift `u : M →ₗ[A] TwistedExt D` of `D.derTwistedExt`. -/
noncomputable def exteriorAlgebraDeriv : ExteriorAlgebra A M →ₗ[R] ExteriorAlgebra A M where
  toFun x := (twistedLift D u hspan hu x).snd
  map_add' x y := congrArg TwistedAlg.snd (map_add (twistedLift D u hspan hu) x y)
  map_smul' r x := by
    have halg : (twistedLift D u hspan hu (algebraMap A _ (algebraMap R A r))).snd = 0 := by
      rw [(twistedLift D u hspan hu).commutes]; simp
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R A, map_mul, TwistedAlg.snd_mul, halg,
      zero_mul, zero_add, fst_twistedLift, CliffordAlgebra.involute.commutes,
      ← IsScalarTower.algebraMap_apply R A, ← Algebra.smul_def]; rfl
private theorem exteriorAlgebraDeriv_apply (x : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu x = (twistedLift D u hspan hu x).snd := (rfl)

@[simp] theorem exteriorAlgebraDeriv_algebraMap (a : A) :
    D.exteriorAlgebraDeriv u hspan hu (algebraMap A (ExteriorAlgebra A M) a) =
      ExteriorAlgebra.ι A (D a) :=
  congrArg TwistedAlg.snd ((twistedLift D u hspan hu).commutes a)
@[simp] theorem exteriorAlgebraDeriv_one : D.exteriorAlgebraDeriv u hspan hu 1 = 0 :=
  congrArg TwistedAlg.snd (map_one (twistedLift D u hspan hu))
theorem exteriorAlgebraDeriv_ι (m : M) :
    D.exteriorAlgebraDeriv u hspan hu (ExteriorAlgebra.ι A m) = ((u m).snd : ExteriorAlgebra A M) :=
  congrArg TwistedAlg.snd (ExteriorAlgebra.lift_ι_apply A _ _ m)
@[simp] theorem exteriorAlgebraDeriv_ι_apply (a : A) :
    D.exteriorAlgebraDeriv u hspan hu (ExteriorAlgebra.ι A (D a)) = 0 := by
  rw [exteriorAlgebraDeriv_ι, hu, snd_derTwistedExt, ZeroMemClass.coe_zero]

/-- **Graded Leibniz rule on `ExteriorAlgebra A M`.** -/
theorem exteriorAlgebraDeriv_mul (x y : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (x * y) = D.exteriorAlgebraDeriv u hspan hu x * y +
      CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x *
        D.exteriorAlgebraDeriv u hspan hu y := by
  simp only [exteriorAlgebraDeriv_apply, map_mul, TwistedAlg.snd_mul, fst_twistedLift]

/-- Graded Leibniz rule when the left factor lies in `⋀[A]^p M`. -/
theorem exteriorAlgebraDeriv_mul_of_mem_exteriorPower {p : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^p M) (y : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (x * y) = D.exteriorAlgebraDeriv u hspan hu x * y +
      (-1 : A) ^ p • (x * D.exteriorAlgebraDeriv u hspan hu y) := by
  rw [exteriorAlgebraDeriv_mul, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower hx,
    smul_mul_assoc]

/-- **Scalar Leibniz rule on `ExteriorAlgebra A M`**: `d (a • x) = ι A (D a) * x + a • d x`. -/
theorem exteriorAlgebraDeriv_smul (a : A) (x : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (a • x) =
      ExteriorAlgebra.ι A (D a) * x + a • D.exteriorAlgebraDeriv u hspan hu x := by
  rw [Algebra.smul_def, exteriorAlgebraDeriv_mul, exteriorAlgebraDeriv_algebraMap,
    CliffordAlgebra.involute.commutes, ← Algebra.smul_def]

/-- The exterior derivative anticommutes with the grade involution on `ExteriorAlgebra A M`. -/
theorem exteriorAlgebraDeriv_involute (x : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x) =
      -CliffordAlgebra.involute (Q := (0 : QuadraticForm A M))
        (D.exteriorAlgebraDeriv u hspan hu x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap _ => simp
  | ι m =>
    rw [CliffordAlgebra.involute_ι, map_neg, exteriorAlgebraDeriv_ι,
      TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower (u m).snd.property]; simp
  | mul _ _ hx hy =>
    rw [map_mul, exteriorAlgebraDeriv_mul, hx, hy, exteriorAlgebraDeriv_mul, map_add, map_mul,
      map_mul, neg_mul, mul_neg, neg_add]
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]

/-- **Ambient-algebra square-zero identity (`d ∘ d = 0`) on `ExteriorAlgebra A M`**, for
pointwise simplification of inhomogeneous elements. -/
@[simp] theorem exteriorAlgebraDeriv_exteriorAlgebraDeriv (x : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (D.exteriorAlgebraDeriv u hspan hu x) = 0 :=
  let δ := D.exteriorAlgebraDeriv u hspan hu
  eq_zero_of_gradedDeriv D hspan id id (δ.toAddMonoidHom.comp δ.toAddMonoidHom)
    (fun y z ↦ by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, id_eq]
      rw [exteriorAlgebraDeriv_mul, map_add, exteriorAlgebraDeriv_mul, exteriorAlgebraDeriv_mul,
        exteriorAlgebraDeriv_involute, CliffordAlgebra.involute_involutive y, neg_mul]; abel)
    (fun _ ↦ by simp [δ]) (fun _ ↦ by simp [δ]) x

/-- **Uniqueness of the exterior derivative on `ExteriorAlgebra A M`.** -/
theorem exteriorAlgebraDeriv_unique (δ' : ExteriorAlgebra A M →ₗ[R] ExteriorAlgebra A M)
    (halg : ∀ a, δ' (algebraMap A _ a) = ExteriorAlgebra.ι A (D a))
    (hd : ∀ a, δ' (ExteriorAlgebra.ι A (D a)) = 0)
    (hmul : ∀ x y, δ' (x * y) =
      δ' x * y + CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x * δ' y) :
    δ' = D.exteriorAlgebraDeriv u hspan hu :=
  let δ := D.exteriorAlgebraDeriv u hspan hu
  LinearMap.ext fun x ↦ sub_eq_zero.mp <| eq_zero_of_gradedDeriv D hspan id
    (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M))) (δ' - δ).toAddMonoidHom
    (fun y z ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply, id_eq]
      rw [hmul, exteriorAlgebraDeriv_mul, sub_mul, mul_sub]; abel)
    (fun a ↦ by simp [δ, halg]) (fun a ↦ by simp [δ, hd]) x

/-- **Semilinear naturality of `exteriorAlgebraDeriv`.** -/
theorem mapSemilinear_exteriorAlgebraDeriv {B N : Type*} [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (D' : Derivation R B N) (u' : N →ₗ[B] TwistedExt D')
    (hspan' : Submodule.span B (Set.range D') = ⊤) (hu' : ∀ b, u' (D' b) = D'.derTwistedExt b)
    (f : A →ₐ[R] B) (g : M →ₛₗ[f.toRingHom] N) (hg : ∀ a, g (D a) = D' (f a))
    (x : ExteriorAlgebra A M) :
    ExteriorAlgebra.mapSemilinear g (D.exteriorAlgebraDeriv u hspan hu x) =
      D'.exteriorAlgebraDeriv u' hspan' hu' (ExteriorAlgebra.mapSemilinear g x) := by
  let Φ := ExteriorAlgebra.mapSemilinear g
  let δ := D.exteriorAlgebraDeriv u hspan hu; let δ' := D'.exteriorAlgebraDeriv u' hspan' hu'
  let Δ := Φ.toAddMonoidHom.comp δ.toAddMonoidHom - δ'.toAddMonoidHom.comp Φ.toAddMonoidHom
  have hΔ (z) : Δ z = Φ (δ z) - δ' (Φ z) := rfl
  refine sub_eq_zero.mp <| eq_zero_of_gradedDeriv D hspan Φ
    (CliffordAlgebra.involute (Q := (0 : QuadraticForm B N)) ∘ Φ) Δ
    (fun y z ↦ by
      simp only [hΔ, Function.comp_apply]
      rw [exteriorAlgebraDeriv_mul, map_add, map_mul, map_mul,
        ExteriorAlgebra.mapSemilinear_involute, map_mul, exteriorAlgebraDeriv_mul, sub_mul,
        mul_sub]; abel)
    (fun a ↦ by
      rw [hΔ, exteriorAlgebraDeriv_algebraMap, ExteriorAlgebra.mapSemilinear_ι,
        ExteriorAlgebra.mapSemilinear_algebraMap, exteriorAlgebraDeriv_algebraMap,
        hg, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, sub_self])
    (fun a ↦ by
      rw [hΔ, exteriorAlgebraDeriv_ι_apply, map_zero, ExteriorAlgebra.mapSemilinear_ι, hg,
        exteriorAlgebraDeriv_ι_apply, sub_self]) x

/-- `exteriorAlgebraDeriv` raises exterior degree by `1`. -/
theorem exteriorAlgebraDeriv_mem_exteriorPower {q : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^q M) : D.exteriorAlgebraDeriv u hspan hu x ∈ ⋀[A]^(q + 1) M := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap a =>
    rw [exteriorAlgebraDeriv_algebraMap]; exact TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _
  | add _ _ _ _ _ ihx ihy => exact map_add (D.exteriorAlgebraDeriv u hspan hu) .. ▸ add_mem ihx ihy
  | mem_mul _ hw i x hx ih =>
    obtain ⟨m, rfl⟩ := hw
    rw [exteriorAlgebraDeriv_mul, exteriorAlgebraDeriv_ι, CliffordAlgebra.involute_ι, neg_mul]
    have h₁ : ((u m).snd : ExteriorAlgebra A M) * x ∈ ⋀[A]^(i + 1 + 1) M :=
      Nat.add_comm 2 i ▸ SetLike.mul_mem_graded (u m).snd.property hx
    exact add_mem h₁ (neg_mem (TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower m ih))

/-- **The `q`-th exterior derivative `⋀[A]^q M →ₗ[R] ⋀[A]^(q + 1) M`** associated to `D` and
`u : M →ₗ[A] TwistedExt D`. -/
noncomputable def exteriorDeriv (q : ℕ) : ⋀[A]^q M →ₗ[R] ⋀[A]^(q + 1) M where
  toFun ω := ⟨D.exteriorAlgebraDeriv u hspan hu ω.val,
    D.exteriorAlgebraDeriv_mem_exteriorPower u hspan hu ω.property⟩
  map_add' ω₁ ω₂ := Subtype.ext (map_add (D.exteriorAlgebraDeriv u hspan hu) ω₁.val ω₂.val)
  map_smul' r ω := Subtype.ext ((D.exteriorAlgebraDeriv u hspan hu).map_smul r ω.val)

@[simp] theorem coe_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q M) :
    (D.exteriorDeriv u hspan hu q ω : ExteriorAlgebra A M) =
      D.exteriorAlgebraDeriv u hspan hu ω.val := (rfl)
@[simp] theorem exteriorDeriv_zero_symm (a : A) :
    D.exteriorDeriv u hspan hu 0 ((exteriorPower.zeroEquiv A M).symm a) =
      (exteriorPower.oneEquiv A M).symm (D a) := Subtype.ext <| by
  simp [exteriorPower.zeroEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_succ_apply, exteriorAlgebraDeriv_smul]
theorem oneEquiv_exteriorDeriv_zero (ω : ⋀[A]^0 M) :
    exteriorPower.oneEquiv A M (D.exteriorDeriv u hspan hu 0 ω) =
      D (exteriorPower.zeroEquiv A M ω) := by
  conv_lhs => rw [← (exteriorPower.zeroEquiv A M).symm_apply_apply ω, exteriorDeriv_zero_symm]
  exact LinearEquiv.apply_symm_apply _ _
/-- **Pointwise homogeneous square-zero identity** `d (d ω) = 0` for a `q`-form `ω`, used for
`simp` rewriting. -/
@[simp] theorem exteriorDeriv_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q M) :
    D.exteriorDeriv u hspan hu (q + 1) (D.exteriorDeriv u hspan hu q ω) = 0 :=
  Subtype.ext (D.exteriorAlgebraDeriv_exteriorAlgebraDeriv u hspan hu ω.val)
/-- **Bundled square-zero composition** `d_{q+1} ∘ₗ d_q = 0` as `R`-linear maps on exterior
powers, used to assemble de Rham cochain complexes. -/
theorem exteriorDeriv_comp_exteriorDeriv (q : ℕ) :
    (D.exteriorDeriv u hspan hu (q + 1)) ∘ₗ (D.exteriorDeriv u hspan hu q) = 0 :=
  LinearMap.ext (D.exteriorDeriv_exteriorDeriv_apply u hspan hu q)
/-- **Scalar Leibniz rule on `⋀[A]^q M`**: `d (a • ω) = D a ∧ ω + a • d ω`. -/
theorem exteriorDeriv_smul (q : ℕ) (a : A) (ω : ⋀[A]^q M) :
    D.exteriorDeriv u hspan hu q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D a) q ω + a • D.exteriorDeriv u hspan hu q ω :=
  Subtype.ext <| by simpa using D.exteriorAlgebraDeriv_smul u hspan hu a ω.val
/-- Every pure wedge product `D b₀ ∧ ⋯ ∧ D b_{q-1}` of exact differentials is closed (`d = 0`). -/
@[simp] theorem exteriorDeriv_ιMulti_comp_D {q : ℕ} (b : Fin q → A) :
    D.exteriorDeriv u hspan hu q (exteriorPower.ιMulti A q (D ∘ b)) = 0 := by
  apply Subtype.ext
  rw [coe_exteriorDeriv_apply, exteriorPower.ιMulti_apply_coe, ZeroMemClass.coe_zero]
  induction q with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, Function.comp_apply, exteriorAlgebraDeriv_mul,
      exteriorAlgebraDeriv_ι_apply, zero_mul, zero_add]
    exact (congrArg _ (ih (Matrix.vecTail b))).trans (mul_zero _)
/-- **Formula on scaled standard generators**: since `D b₀ ∧ ⋯ ∧ D b_{q-1}` is closed, only
its scalar coefficient `a` is differentiated:
`d (a • (D b₀ ∧ ⋯ ∧ D b_{q-1})) = D a ∧ D b₀ ∧ ⋯ ∧ D b_{q-1}`. -/
theorem exteriorDeriv_smul_ιMulti_comp_D {q : ℕ} (a : A) (b : Fin q → A) :
    D.exteriorDeriv u hspan hu q (a • exteriorPower.ιMulti A q (D ∘ b)) =
      exteriorPower.ιMulti A (q + 1) (Fin.cons (D a) (D ∘ b)) := by
  rw [exteriorDeriv_smul, exteriorDeriv_ιMulti_comp_D, smul_zero, add_zero,
    TauCeti.ExteriorAlgebra.wedgeLeft_ιMulti]
/-- **Graded Leibniz rule on `exteriorPower.wedge`.** -/
theorem exteriorDeriv_wedge (p q : ℕ) (ω : ⋀[A]^p M) (η : ⋀[A]^q M) :
    D.exteriorDeriv u hspan hu (p + q) (exteriorPower.wedge A M p q ω η) =
      LinearEquiv.ofEq _ _ (congrArg (⋀[A]^· M) (Nat.add_right_comm p 1 q))
        (exteriorPower.wedge A M (p + 1) q (D.exteriorDeriv u hspan hu p ω) η) +
        (-1 : A) ^ p • exteriorPower.wedge A M p (q + 1) ω (D.exteriorDeriv u hspan hu q η) :=
  Subtype.ext <| by
    simpa using D.exteriorAlgebraDeriv_mul_of_mem_exteriorPower u hspan hu ω.property η.val
/-- **Semilinear naturality of `exteriorDeriv`.** -/
theorem mapSemilinear_exteriorDeriv {B N : Type*} [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (D' : Derivation R B N) (u' : N →ₗ[B] TwistedExt D')
    (hspan' : Submodule.span B (Set.range D') = ⊤) (hu' : ∀ b, u' (D' b) = D'.derTwistedExt b)
    (f : A →ₐ[R] B) (g : M →ₛₗ[f.toRingHom] N) (hg : ∀ a, g (D a) = D' (f a))
    (q : ℕ) (ω : ⋀[A]^q M) :
    exteriorPower.mapSemilinear (q + 1) g (D.exteriorDeriv u hspan hu q ω) =
      D'.exteriorDeriv u' hspan' hu' q (exteriorPower.mapSemilinear q g ω) := Subtype.ext <| by
  simp only [exteriorPower.coe_mapSemilinear_apply, coe_exteriorDeriv_apply]
  exact mapSemilinear_exteriorAlgebraDeriv D u hspan hu D' u' hspan' hu' f g hg ω.val
end ExteriorDeriv
end Derivation
