/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.MapSemilinear
public import TauCeti.LinearAlgebra.ExteriorPower.Noetherian
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.Basic

/-!
# Exterior derivative associated to a generating derivation with a twisted lift

Let `D : Derivation R A M` be an `R`-derivation whose image spans `M` over `A`. Whenever the
twisted `A`-module `TwistedExt D = M × ⋀[A]^2 M` with `a • (m, ω) = (a • m, D a ∧ m + a • ω)`
receives an `A`-linear lift `u : M →ₗ[A] TwistedExt D` of `D.derTwistedExt`, there is a unique
square-zero degree-`+1` graded `R`-derivation `Derivation.extDeriv` on `ExteriorAlgebra A M`
sending a scalar `algebraMap A _ a` to `ExteriorAlgebra.ι A (D a)` and a degree-one generator
`ExteriorAlgebra.ι A m` to `(u m).snd`, restricting to `Derivation.exteriorPowerDeriv` on
exterior powers `⋀[A]^q M`, with no bases, smoothness, or characteristic hypotheses.
-/

public section
namespace Derivation

/-- **The twisted extension `M × ⋀[A]^2 M` associated to a derivation `D : Derivation R A M`.**
As an abelian group it is `M × ⋀[A]^2 M`, with `a • (m, ω) = (a • m, D a ∧ m + a • ω)`. When the
image of `D` spans `M` over `A`, an `A`-linear map `u : M →ₗ[A] TwistedExt D` satisfying
`u (D a) = (D a, 0)` for all `a` is automatically a section of `fstLinear D` and determines a
unique square-zero degree-`+1` graded `R`-derivation on `ExteriorAlgebra A M` sending
`algebraMap A _ a` to `ExteriorAlgebra.ι A (D a)` and `ExteriorAlgebra.ι A m` to `(u m).snd`. -/
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

/-- The image of `inl D` equals the kernel of `fstLinear D`. -/
theorem range_inl_eq_ker_fstLinear (D : Derivation R A M) :
    LinearMap.range (inl D) = LinearMap.ker (fstLinear D) :=
  Submodule.ext fun x ↦ ⟨by rintro ⟨ω, rfl⟩; rfl, fun hx ↦ ⟨x.snd, TwistedExt.ext hx.symm rfl⟩⟩

/-- Exactness of `0 → ⋀[A]^2 M → TwistedExt D → M → 0` at `TwistedExt D`. -/
theorem exact_inl_fstLinear (D : Derivation R A M) :
    Function.Exact (inl D) (fstLinear D) :=
  LinearMap.exact_iff.mpr (range_inl_eq_ker_fstLinear D).symm

/-- `fstLinear D : TwistedExt D →ₗ[A] M` is surjective. -/
theorem fstLinear_surjective (D : Derivation R A M) :
    Function.Surjective (fstLinear D) :=
  fun m ↦ ⟨⟨m, 0⟩, rfl⟩

/-- `TwistedExt D` is a finite `A`-module whenever `M` is. -/
instance [Module.Finite A M] : Module.Finite A (TwistedExt D) :=
  Module.Finite.of_exact (exact_inl_fstLinear D) (fstLinear_surjective D)
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

private noncomputable def twistedExtSnd (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D) :
    M →ₗ[R] ExteriorAlgebra A M where
  toFun m := ((u m).snd : ExteriorAlgebra A M)
  map_add' m₁ m₂ := by simp [u.map_add]
  map_smul' r m := by
    rw [RingHom.id_apply, ← IsScalarTower.algebraMap_smul A r m, u.map_smul,
      TwistedExt.snd_smul, Derivation.map_algebraMap]
    simp

private theorem twistedExtSnd_smul (hspan : Submodule.span A (Set.range D) = ⊤)
    (hu : ∀ a, u (D a) = D.derTwistedExt a) (a : A) (m : M) :
    twistedExtSnd D u (a • m) =
      ((ExteriorAlgebra.ι A).compDer D) a * ExteriorAlgebra.ι A m + a • twistedExtSnd D u m := by
  simp [twistedExtSnd, u.map_smul, TwistedExt.snd_smul, fst_lift_eq_id D u hspan hu m]

private theorem twistedExtSnd_sq (m : M) :
    twistedExtSnd D u m * ExteriorAlgebra.ι A m +
      CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) (ExteriorAlgebra.ι A m) *
        twistedExtSnd D u m = 0 := by
  simp only [twistedExtSnd, LinearMap.coe_mk, AddHom.coe_mk]
  rw [CliffordAlgebra.involute_ι, neg_mul,
    ExteriorAlgebra.ι_mul_eq_involute_mul m ((u m).snd : ExteriorAlgebra A M),
    TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower (u m).snd.property]
  simp

include D u hspan hu in
/-- **The graded exterior derivative on `ExteriorAlgebra A M`** associated to `D` and an
`A`-linear lift `u : M →ₗ[A] TwistedExt D` of `D.derTwistedExt`. -/
noncomputable def extDeriv : ExteriorAlgebra A M →ₗ[R] ExteriorAlgebra A M :=
  ExteriorAlgebra.liftTwistedDerivation
    (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)))
    ((ExteriorAlgebra.ι A).compDer D)
    (fun a m ↦ by
      simpa using ExteriorAlgebra.ι_mul_eq_involute_mul (D a) (ExteriorAlgebra.ι A m))
    (twistedExtSnd D u)
    (twistedExtSnd_smul D u hspan hu)
    (twistedExtSnd_sq D u)

@[simp] theorem extDeriv_algebraMap (a : A) :
    D.extDeriv u hspan hu (algebraMap A (ExteriorAlgebra A M) a) =
      ExteriorAlgebra.ι A (D a) :=
  ExteriorAlgebra.liftTwistedDerivation_algebraMap _ _ _ _ _ _ a
@[simp] theorem extDeriv_one : D.extDeriv u hspan hu 1 = 0 :=
  ExteriorAlgebra.liftTwistedDerivation_one _ _ _ _ _ _
theorem extDeriv_ι (m : M) :
    D.extDeriv u hspan hu (ExteriorAlgebra.ι A m) = ((u m).snd : ExteriorAlgebra A M) :=
  ExteriorAlgebra.liftTwistedDerivation_ι _ _ _ _ _ _ m
@[simp] theorem extDeriv_ι_D (a : A) :
    D.extDeriv u hspan hu (ExteriorAlgebra.ι A (D a)) = 0 := by
  rw [extDeriv_ι, hu, snd_derTwistedExt, ZeroMemClass.coe_zero]

/-- **Graded Leibniz rule on `ExteriorAlgebra A M`.** -/
theorem extDeriv_mul (x y : ExteriorAlgebra A M) :
    D.extDeriv u hspan hu (x * y) = D.extDeriv u hspan hu x * y +
      CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x *
        D.extDeriv u hspan hu y :=
  ExteriorAlgebra.liftTwistedDerivation_mul _ _ _ _ _ _ x y

/-- Graded Leibniz rule when the left factor lies in `⋀[A]^p M`. -/
theorem extDeriv_mul_of_mem_exteriorPower {p : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^p M) (y : ExteriorAlgebra A M) :
    D.extDeriv u hspan hu (x * y) = D.extDeriv u hspan hu x * y +
      (-1 : A) ^ p • (x * D.extDeriv u hspan hu y) := by
  rw [extDeriv_mul, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower hx,
    smul_mul_assoc]

/-- **Scalar Leibniz rule on `ExteriorAlgebra A M`**: `d (a • x) = ι A (D a) * x + a • d x`. -/
theorem extDeriv_smul (a : A) (x : ExteriorAlgebra A M) :
    D.extDeriv u hspan hu (a • x) =
      ExteriorAlgebra.ι A (D a) * x + a • D.extDeriv u hspan hu x :=
  ExteriorAlgebra.liftTwistedDerivation_smul _ _ _ _ _ _ a x

/-- The exterior derivative anticommutes with the grade involution on `ExteriorAlgebra A M`. -/
theorem extDeriv_involute (x : ExteriorAlgebra A M) :
    D.extDeriv u hspan hu (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x) =
      -CliffordAlgebra.involute (Q := (0 : QuadraticForm A M))
        (D.extDeriv u hspan hu x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap _ => simp
  | ι m =>
    rw [CliffordAlgebra.involute_ι, map_neg, extDeriv_ι,
      TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower (u m).snd.property]; simp
  | mul _ _ hx hy =>
    rw [map_mul, extDeriv_mul, hx, hy, extDeriv_mul, map_add, map_mul,
      map_mul, neg_mul, mul_neg, neg_add]
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]

/-- **Ambient-algebra square-zero identity (`d ∘ d = 0`) on `ExteriorAlgebra A M`**, for
pointwise simplification of inhomogeneous elements. -/
@[simp] theorem extDeriv_extDeriv (x : ExteriorAlgebra A M) :
    D.extDeriv u hspan hu (D.extDeriv u hspan hu x) = 0 :=
  let δ := D.extDeriv u hspan hu
  eq_zero_of_gradedDeriv D hspan id id (δ.toAddMonoidHom.comp δ.toAddMonoidHom)
    (fun y z ↦ by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, id_eq]
      rw [extDeriv_mul, map_add, extDeriv_mul, extDeriv_mul,
        extDeriv_involute, CliffordAlgebra.involute_involutive y, neg_mul]; abel)
    (fun _ ↦ by simp [δ]) (fun _ ↦ by simp [δ]) x

/-- **Uniqueness of the exterior derivative on `ExteriorAlgebra A M`.** -/
theorem extDeriv_unique (δ' : ExteriorAlgebra A M →ₗ[R] ExteriorAlgebra A M)
    (halg : ∀ a, δ' (algebraMap A _ a) = ExteriorAlgebra.ι A (D a))
    (hd : ∀ a, δ' (ExteriorAlgebra.ι A (D a)) = 0)
    (hmul : ∀ x y, δ' (x * y) =
      δ' x * y + CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x * δ' y) :
    δ' = D.extDeriv u hspan hu :=
  let δ := D.extDeriv u hspan hu
  LinearMap.ext fun x ↦ sub_eq_zero.mp <| eq_zero_of_gradedDeriv D hspan id
    (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M))) (δ' - δ).toAddMonoidHom
    (fun y z ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply, id_eq]
      rw [hmul, extDeriv_mul, sub_mul, mul_sub]; abel)
    (fun a ↦ by simp [δ, halg]) (fun a ↦ by simp [δ, hd]) x

/-- **Semilinear naturality of `extDeriv`.** -/
theorem mapSemilinear_extDeriv {B N : Type*} [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (D' : Derivation R B N) (u' : N →ₗ[B] TwistedExt D')
    (hspan' : Submodule.span B (Set.range D') = ⊤) (hu' : ∀ b, u' (D' b) = D'.derTwistedExt b)
    (f : A →ₐ[R] B) (g : M →ₛₗ[f.toRingHom] N) (hg : ∀ a, g (D a) = D' (f a))
    (x : ExteriorAlgebra A M) :
    ExteriorAlgebra.mapSemilinear g (D.extDeriv u hspan hu x) =
      D'.extDeriv u' hspan' hu' (ExteriorAlgebra.mapSemilinear g x) := by
  let Φ := ExteriorAlgebra.mapSemilinear g
  let δ := D.extDeriv u hspan hu; let δ' := D'.extDeriv u' hspan' hu'
  let Δ := Φ.toAddMonoidHom.comp δ.toAddMonoidHom - δ'.toAddMonoidHom.comp Φ.toAddMonoidHom
  have hΔ (z) : Δ z = Φ (δ z) - δ' (Φ z) := rfl
  refine sub_eq_zero.mp <| eq_zero_of_gradedDeriv D hspan Φ
    (CliffordAlgebra.involute (Q := (0 : QuadraticForm B N)) ∘ Φ) Δ
    (fun y z ↦ by
      simp only [hΔ, Function.comp_apply]
      rw [extDeriv_mul, map_add, map_mul, map_mul,
        ExteriorAlgebra.mapSemilinear_involute, map_mul, extDeriv_mul, sub_mul,
        mul_sub]; abel)
    (fun a ↦ by
      rw [hΔ, extDeriv_algebraMap, ExteriorAlgebra.mapSemilinear_ι,
        ExteriorAlgebra.mapSemilinear_algebraMap, extDeriv_algebraMap,
        hg, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, sub_self])
    (fun a ↦ by
      rw [hΔ, extDeriv_ι_D, map_zero, ExteriorAlgebra.mapSemilinear_ι, hg,
        extDeriv_ι_D, sub_self]) x

/-- `extDeriv` raises exterior degree by `1`. -/
theorem extDeriv_mem_exteriorPower {q : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^q M) : D.extDeriv u hspan hu x ∈ ⋀[A]^(q + 1) M :=
  ExteriorAlgebra.liftTwistedDerivation_mem_exteriorPower _ _ _ _ _ _ (r := 1)
    (fun m ↦ by
      rw [CliffordAlgebra.involute_ι]
      exact neg_mem (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one m))
    (fun a ↦ TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _)
    (fun m ↦ (u m).snd.property) hx

/-- **The `q`-th exterior derivative `⋀[A]^q M →ₗ[R] ⋀[A]^(q + 1) M`** associated to `D` and
`u : M →ₗ[A] TwistedExt D`. -/
noncomputable def exteriorPowerDeriv (q : ℕ) : ⋀[A]^q M →ₗ[R] ⋀[A]^(q + 1) M where
  toFun ω := ⟨D.extDeriv u hspan hu ω.val,
    D.extDeriv_mem_exteriorPower u hspan hu ω.property⟩
  map_add' ω₁ ω₂ := Subtype.ext (map_add (D.extDeriv u hspan hu) ω₁.val ω₂.val)
  map_smul' r ω := Subtype.ext ((D.extDeriv u hspan hu).map_smul r ω.val)

@[simp] theorem coe_exteriorPowerDeriv_apply (q : ℕ) (ω : ⋀[A]^q M) :
    (D.exteriorPowerDeriv u hspan hu q ω : ExteriorAlgebra A M) =
      D.extDeriv u hspan hu ω.val := (rfl)
/-- **Degree-zero identification (`simp` direction)**: under `zeroEquiv` and `oneEquiv`,
`D.exteriorPowerDeriv u hspan hu 0` identifies with `D`, rewriting `(zeroEquiv A M).symm a` to
`(oneEquiv A M).symm (D a)`. See `oneEquiv_exteriorPowerDeriv_zero` for the unapplied equivalence
direction extracting `D`. -/
@[simp] theorem exteriorPowerDeriv_zero_zeroEquiv_symm (a : A) :
    D.exteriorPowerDeriv u hspan hu 0 ((exteriorPower.zeroEquiv A M).symm a) =
      (exteriorPower.oneEquiv A M).symm (D a) := Subtype.ext <| by
  simp [exteriorPower.zeroEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_succ_apply, extDeriv_smul]
/-- **Degree-zero identification (forward-equivalence direction)**: under `zeroEquiv` and
`oneEquiv`, `D.exteriorPowerDeriv u hspan hu 0` recovers `D` as
`oneEquiv A M (d ω) = D (zeroEquiv A M ω)`. See `exteriorPowerDeriv_zero_zeroEquiv_symm` for the
`simp` direction. -/
theorem oneEquiv_exteriorPowerDeriv_zero (ω : ⋀[A]^0 M) :
    exteriorPower.oneEquiv A M (D.exteriorPowerDeriv u hspan hu 0 ω) =
      D (exteriorPower.zeroEquiv A M ω) := by
  conv_lhs =>
    rw [← (exteriorPower.zeroEquiv A M).symm_apply_apply ω, exteriorPowerDeriv_zero_zeroEquiv_symm]
  exact LinearEquiv.apply_symm_apply _ _
/-- **Pointwise homogeneous square-zero identity** `d (d ω) = 0` for a `q`-form `ω`, used for
`simp` rewriting. -/
@[simp] theorem exteriorPowerDeriv_exteriorPowerDeriv_apply (q : ℕ) (ω : ⋀[A]^q M) :
    D.exteriorPowerDeriv u hspan hu (q + 1) (D.exteriorPowerDeriv u hspan hu q ω) = 0 :=
  Subtype.ext (D.extDeriv_extDeriv u hspan hu ω.val)
/-- **Bundled square-zero composition** `d_{q+1} ∘ₗ d_q = 0` as `R`-linear maps on exterior
powers, used to assemble de Rham cochain complexes. -/
theorem exteriorPowerDeriv_comp_exteriorPowerDeriv (q : ℕ) :
    (D.exteriorPowerDeriv u hspan hu (q + 1)) ∘ₗ (D.exteriorPowerDeriv u hspan hu q) = 0 :=
  LinearMap.ext (D.exteriorPowerDeriv_exteriorPowerDeriv_apply u hspan hu q)
/-- **Scalar Leibniz rule on `⋀[A]^q M`**: `d (a • ω) = D a ∧ ω + a • d ω`. -/
theorem exteriorPowerDeriv_smul (q : ℕ) (a : A) (ω : ⋀[A]^q M) :
    D.exteriorPowerDeriv u hspan hu q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D a) q ω + a • D.exteriorPowerDeriv u hspan hu q ω :=
  Subtype.ext <| by simpa using D.extDeriv_smul u hspan hu a ω.val
/-- Every pure wedge product `D b₀ ∧ ⋯ ∧ D b_{q-1}` of exact differentials is closed (`d = 0`). -/
@[simp] theorem exteriorPowerDeriv_ιMulti_comp_D {q : ℕ} (b : Fin q → A) :
    D.exteriorPowerDeriv u hspan hu q (exteriorPower.ιMulti A q (D ∘ b)) = 0 := by
  apply Subtype.ext
  rw [coe_exteriorPowerDeriv_apply, exteriorPower.ιMulti_apply_coe, ZeroMemClass.coe_zero]
  induction q with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, Function.comp_apply, extDeriv_mul,
      extDeriv_ι_D, zero_mul, zero_add]
    exact (congrArg _ (ih (Matrix.vecTail b))).trans (mul_zero _)
/-- **Formula on scaled standard generators**: since `D b₀ ∧ ⋯ ∧ D b_{q-1}` is closed, only
its scalar coefficient `a` is differentiated:
`d (a • (D b₀ ∧ ⋯ ∧ D b_{q-1})) = D a ∧ D b₀ ∧ ⋯ ∧ D b_{q-1}`. -/
theorem exteriorPowerDeriv_smul_ιMulti_comp_D {q : ℕ} (a : A) (b : Fin q → A) :
    D.exteriorPowerDeriv u hspan hu q (a • exteriorPower.ιMulti A q (D ∘ b)) =
      exteriorPower.ιMulti A (q + 1) (Fin.cons (D a) (D ∘ b)) := by
  rw [exteriorPowerDeriv_smul, exteriorPowerDeriv_ιMulti_comp_D, smul_zero, add_zero,
    TauCeti.ExteriorAlgebra.wedgeLeft_ιMulti]
/-- **Graded Leibniz rule on `exteriorPower.wedge`.** -/
theorem exteriorPowerDeriv_wedge (p q : ℕ) (ω : ⋀[A]^p M) (η : ⋀[A]^q M) :
    D.exteriorPowerDeriv u hspan hu (p + q) (exteriorPower.wedge A M p q ω η) =
      LinearEquiv.ofEq _ _ (congrArg (⋀[A]^· M) (Nat.add_right_comm p 1 q))
        (exteriorPower.wedge A M (p + 1) q (D.exteriorPowerDeriv u hspan hu p ω) η) +
        (-1 : A) ^ p •
          exteriorPower.wedge A M p (q + 1) ω (D.exteriorPowerDeriv u hspan hu q η) :=
  Subtype.ext <| by
    simpa using D.extDeriv_mul_of_mem_exteriorPower u hspan hu ω.property η.val
/-- **Semilinear naturality of `exteriorPowerDeriv`.** -/
theorem mapSemilinear_exteriorPowerDeriv {B N : Type*} [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (D' : Derivation R B N) (u' : N →ₗ[B] TwistedExt D')
    (hspan' : Submodule.span B (Set.range D') = ⊤) (hu' : ∀ b, u' (D' b) = D'.derTwistedExt b)
    (f : A →ₐ[R] B) (g : M →ₛₗ[f.toRingHom] N) (hg : ∀ a, g (D a) = D' (f a))
    (q : ℕ) (ω : ⋀[A]^q M) :
    exteriorPower.mapSemilinear (q + 1) g (D.exteriorPowerDeriv u hspan hu q ω) =
      D'.exteriorPowerDeriv u' hspan' hu' q (exteriorPower.mapSemilinear q g ω) := Subtype.ext <| by
  simp only [exteriorPower.coe_mapSemilinear_apply, coe_exteriorPowerDeriv_apply]
  exact mapSemilinear_extDeriv D u hspan hu D' u' hspan' hu' f g hg ω.val
end ExteriorDeriv
end Derivation
