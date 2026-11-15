/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.MapSemilinear
public import TauCeti.LinearAlgebra.ExteriorPower.Noetherian
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import Mathlib.RingTheory.Finiteness.Finsupp
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Exterior derivative associated to a universal derivation

Let `R → A` be a homomorphism of commutative rings and `D : Derivation R A M` an `R`-derivation
whose image spans `M` over `A`. Whenever the twisted `A`-module `TwistedExt D = M × ⋀[A]^2 M`
with scalar action `a • (m, ω) = (a • m, D a ∧ m + a • ω)` receives an `A`-linear lift of the
`R`-derivation `derTwistedExt D : a ↦ (D a, 0)`, its second component `d₁ : M → ⋀[A]^2 M` extends
uniquely to an `R`-linear graded derivation of degree `+1` on `ExteriorAlgebra A M` with square
zero.

The construction avoids bases, smoothness hypotheses, and characteristic assumptions (including
characteristic `2`):

1. `derTwistedExt D` satisfies the Leibniz rule in every characteristic because
   `D a ∧ D b + D b ∧ D a = 0` in `⋀[A]^2 M`. Moreover, `TwistedExt D` is a finite `A`-module as
   soon as `M` is, via the short exact sequence `0 → ⋀[A]^2 M → TwistedExt D → M → 0`.
2. Equipping `ExteriorAlgebra A M × ExteriorAlgebra A M` with the grade-twisted square-zero
   multiplication `(x₁, y₁) * (x₂, y₂) = (x₁ * x₂, y₁ * x₂ + involute x₁ * y₂)` and the central
   `A`-algebra map `a ↦ (algebraMap a, ι (D a))`, the map `m ↦ (ι m, d₁ m)` is `A`-linear and
   squares to zero because `d₁ m ∈ ⋀[A]^2 M` is fixed by the grade involution. The universal
   property of `ExteriorAlgebra A M` produces `exteriorAlgebraDeriv`.
3. Anticommutation with `involute` turns `δ ∘ δ` into an *ungraded* derivation of
   `ExteriorAlgebra A M`, so `m ↦ δ (δ (ι m))` is `A`-linear and vanishes on `Set.range D`, hence
   everywhere since `Set.range D` spans `M`. The same linearity argument proves uniqueness and
   semilinear naturality.

Specialising to `KaehlerDifferential.D R A` constructs the algebraic exterior derivative
`KaehlerDifferential.exteriorDeriv R A q : ⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R]` for every
`R`-algebra `A`.

## Main definitions

* `Derivation.TwistedExt`, `Derivation.derTwistedExt`: the twisted extension `M × ⋀[A]^2 M` and
  its canonical `R`-derivation `a ↦ (D a, 0)`.
* `Derivation.exteriorAlgebraDeriv`, `Derivation.exteriorDeriv`: the graded `R`-linear exterior
  derivative on `ExteriorAlgebra A M` and on each exterior power `⋀[A]^q M`.
* `KaehlerDifferential.exteriorAlgebraDeriv`, `KaehlerDifferential.exteriorDeriv`: the exterior
  derivative on algebraic Kähler forms.
-/

public section

namespace Derivation

section TwistedExt

/-- **The twisted extension `M × ⋀[A]^2 M` associated to a derivation `D : Derivation R A M`.**
As an abelian group it is `M × ⋀[A]^2 M`, while `a : A` acts by
`a • (m, ω) = (a • m, D a ∧ m + a • ω)`. An `A`-linear section of the first projection lifting
`a ↦ (D a, 0)` is equivalent to a degree-`1` exterior differential `M → ⋀[A]^2 M`. -/
@[ext]
structure TwistedExt {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] (_D : Derivation R A M) where
  /-- The `M`-component of an element of `TwistedExt D`. -/
  fst : M
  /-- The `⋀[A]^2 M`-component of an element of `TwistedExt D`. -/
  snd : ⋀[A]^2 M

namespace TwistedExt

section ModuleA

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] {D : Derivation R A M}

instance : Zero (TwistedExt D) := ⟨⟨0, 0⟩⟩
instance : Add (TwistedExt D) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (TwistedExt D) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
instance : Sub (TwistedExt D) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩

@[simp] theorem fst_zero : (0 : TwistedExt D).fst = 0 := (rfl)
@[simp] theorem snd_zero : (0 : TwistedExt D).snd = 0 := (rfl)
@[simp] theorem fst_add (x y : TwistedExt D) : (x + y).fst = x.fst + y.fst := (rfl)
@[simp] theorem snd_add (x y : TwistedExt D) : (x + y).snd = x.snd + y.snd := (rfl)
@[simp] theorem fst_neg (x : TwistedExt D) : (-x).fst = -x.fst := (rfl)
@[simp] theorem snd_neg (x : TwistedExt D) : (-x).snd = -x.snd := (rfl)
@[simp] theorem fst_sub (x y : TwistedExt D) : (x - y).fst = x.fst - y.fst := (rfl)
@[simp] theorem snd_sub (x y : TwistedExt D) : (x - y).snd = x.snd - y.snd := (rfl)

instance : AddCommGroup (TwistedExt D) where
  nsmul n x := ⟨n • x.fst, n • x.snd⟩
  zsmul n x := ⟨n • x.fst, n • x.snd⟩
  add_assoc _ _ _ := TwistedExt.ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add _ := TwistedExt.ext (zero_add _) (zero_add _)
  add_zero _ := TwistedExt.ext (add_zero _) (add_zero _)
  nsmul_zero _ := TwistedExt.ext (zero_smul ℕ _) (zero_smul ℕ _)
  nsmul_succ _ _ := TwistedExt.ext (succ_nsmul _ _) (succ_nsmul _ _)
  zsmul_zero' _ := TwistedExt.ext (zero_smul ℤ _) (zero_smul ℤ _)
  zsmul_succ' n _ := TwistedExt.ext (SubNegMonoid.zsmul_succ' n _) (SubNegMonoid.zsmul_succ' n _)
  zsmul_neg' n _ := TwistedExt.ext (SubNegMonoid.zsmul_neg' n _) (SubNegMonoid.zsmul_neg' n _)
  sub_eq_add_neg _ _ := TwistedExt.ext (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
  neg_add_cancel _ := TwistedExt.ext (neg_add_cancel _) (neg_add_cancel _)
  add_comm _ _ := TwistedExt.ext (add_comm _ _) (add_comm _ _)

noncomputable instance : SMul A (TwistedExt D) where
  smul a x := ⟨a • x.fst, exteriorPower.ιMulti A 2 ![D a, x.fst] + a • x.snd⟩

@[simp]
theorem fst_smul (a : A) (x : TwistedExt D) : (a • x).fst = a • x.fst := (rfl)

@[simp]
theorem snd_smul (a : A) (x : TwistedExt D) :
    (a • x).snd = exteriorPower.ιMulti A 2 ![D a, x.fst] + a • x.snd := (rfl)

theorem coe_ιMulti_two (u v : M) :
    (exteriorPower.ιMulti A 2 ![u, v] : ExteriorAlgebra A M) =
      ExteriorAlgebra.ι A u * ExteriorAlgebra.ι A v := by
  simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, Matrix.vecTail]

noncomputable instance : Module A (TwistedExt D) where
  one_smul x := TwistedExt.ext (one_smul A x.fst) <| Subtype.ext <| by simp
  mul_smul a b x := TwistedExt.ext (mul_smul a b x.fst) <| Subtype.ext <| by
    simp only [snd_smul, fst_smul, Submodule.coe_add, SetLike.val_smul, coe_ιMulti_two,
      D.leibniz, map_add, LinearMap.map_smul, add_mul, smul_mul_assoc, mul_smul_comm,
      smul_add, mul_smul]
    abel
  smul_zero a := TwistedExt.ext (smul_zero a) <| Subtype.ext <| by simp
  smul_add a x y := TwistedExt.ext (smul_add a x.fst y.fst) <| Subtype.ext <| by
    simp only [snd_smul, fst_add, snd_add, Submodule.coe_add, SetLike.val_smul, coe_ιMulti_two,
      map_add, mul_add, smul_add]
    abel
  add_smul a b x := TwistedExt.ext (add_smul a b x.fst) <| Subtype.ext <| by
    simp only [snd_smul, snd_add, Submodule.coe_add, SetLike.val_smul, coe_ιMulti_two,
      map_add, add_mul, add_smul]
    abel
  zero_smul x := TwistedExt.ext (zero_smul A x.fst) <| Subtype.ext <| by simp

/-- The `A`-linear inclusion `⋀[A]^2 M →ₗ[A] TwistedExt D`, `ω ↦ (0, ω)`. -/
noncomputable def inl (D : Derivation R A M) : ⋀[A]^2 M →ₗ[A] TwistedExt D where
  toFun ω := ⟨0, ω⟩
  map_add' _ _ := TwistedExt.ext (by simp) rfl
  map_smul' _ _ := TwistedExt.ext (by simp) <| Subtype.ext <| by simp

@[simp] theorem fst_inl (D : Derivation R A M) (ω : ⋀[A]^2 M) : (inl D ω).fst = 0 := (rfl)
@[simp] theorem snd_inl (D : Derivation R A M) (ω : ⋀[A]^2 M) : (inl D ω).snd = ω := (rfl)

/-- The `A`-linear first projection `TwistedExt D →ₗ[A] M`. -/
def fstLinear (D : Derivation R A M) : TwistedExt D →ₗ[A] M where
  toFun := fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem fstLinear_apply (x : TwistedExt D) : fstLinear D x = x.fst := (rfl)

/-- `TwistedExt D` is a finite `A`-module whenever `M` is, via the short exact sequence
`0 → ⋀[A]^2 M → TwistedExt D → M → 0`. -/
instance [Module.Finite A M] : Module.Finite A (TwistedExt D) := by
  refine Module.Finite.of_exact (f := inl D) (g := fstLinear D) (fun x ↦ ?_) fun m ↦ ⟨⟨m, 0⟩, rfl⟩
  change fstLinear D x = 0 ↔ x ∈ LinearMap.range (inl D)
  rw [fstLinear_apply, LinearMap.mem_range]
  exact ⟨fun hx ↦ ⟨x.snd, TwistedExt.ext hx.symm rfl⟩, by rintro ⟨ω, rfl⟩; rfl⟩

/-- `TwistedExt D` is a Noetherian `A`-module whenever `M` is, without assuming `A` is a
Noetherian ring. -/
instance [IsNoetherian A M] : IsNoetherian A (TwistedExt D) := by
  refine isNoetherian_of_range_eq_ker (inl D) (fstLinear D) ?_
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker, fstLinear_apply]
  exact ⟨by rintro ⟨ω, rfl⟩; rfl, fun hx ↦ ⟨x.snd, TwistedExt.ext hx.symm rfl⟩⟩

end ModuleA

section Tower

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] {D : Derivation R A M}

noncomputable instance : Module R (TwistedExt D) :=
  Module.compHom (TwistedExt D) (algebraMap R A)

instance : IsScalarTower R A (TwistedExt D) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

@[simp]
theorem fst_smul_base (r : R) (x : TwistedExt D) : (r • x).fst = r • x.fst :=
  algebraMap_smul A r x.fst

@[simp]
theorem snd_smul_base (r : R) (x : TwistedExt D) : (r • x).snd = r • x.snd := by
  change (algebraMap R A r • x).snd = r • x.snd
  rw [snd_smul]
  apply Subtype.ext
  simp [algebraMap_smul]

end Tower

end TwistedExt

section DerTwistedExt

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- **The canonical `R`-derivation `A → TwistedExt D`**, sending `a` to `(D a, 0)`. Its Leibniz
rule holds in all characteristics since `D a ∧ D b + D b ∧ D a = 0` in `⋀[A]^2 M`. -/
noncomputable def derTwistedExt (D : Derivation R A M) : Derivation R A (TwistedExt D) where
  toFun a := ⟨D a, 0⟩
  map_add' _ _ := TwistedExt.ext (by simp) (by simp)
  map_smul' _ _ := TwistedExt.ext (by simp) (by simp)
  map_one_eq_zero' := TwistedExt.ext (by simp) rfl
  leibniz' _ _ := TwistedExt.ext (by simp [D.leibniz]) <| Subtype.ext <| by
    simp [ExteriorAlgebra.ι_add_mul_swap]

@[simp]
theorem fst_derTwistedExt (D : Derivation R A M) (a : A) :
    (D.derTwistedExt a).fst = D a := (rfl)

@[simp]
theorem snd_derTwistedExt (D : Derivation R A M) (a : A) :
    (D.derTwistedExt a).snd = 0 := (rfl)

end DerTwistedExt

end TwistedExt

/-! ### Construction of the graded exterior derivative -/

section TwistedAlgSection

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]

/-- Auxiliary grade-twisted square-zero algebra on `ExteriorAlgebra A M × ExteriorAlgebra A M`
with multiplication `(x₁, y₁) * (x₂, y₂) = (x₁ * x₂, y₁ * x₂ + involute x₁ * y₂)` and `A`-algebra
map `a ↦ (algebraMap a, ι (D a))`. -/
@[ext]
private structure TwistedAlg (_D : Derivation R A M) where
  fst : ExteriorAlgebra A M
  snd : ExteriorAlgebra A M

namespace TwistedAlg

variable {D : Derivation R A M}

private instance : Zero (TwistedAlg D) := ⟨⟨0, 0⟩⟩
private instance : One (TwistedAlg D) := ⟨⟨1, 0⟩⟩
private instance : Add (TwistedAlg D) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private instance : Neg (TwistedAlg D) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
private instance : Sub (TwistedAlg D) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩

private noncomputable instance : Mul (TwistedAlg D) where
  mul x y := ⟨x.fst * y.fst,
    x.snd * y.fst + CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x.fst * y.snd⟩

@[simp] private theorem fst_zero : (0 : TwistedAlg D).fst = 0 := (rfl)
@[simp] private theorem snd_zero : (0 : TwistedAlg D).snd = 0 := (rfl)
@[simp] private theorem fst_one : (1 : TwistedAlg D).fst = 1 := (rfl)
@[simp] private theorem snd_one : (1 : TwistedAlg D).snd = 0 := (rfl)
@[simp] private theorem fst_add (x y : TwistedAlg D) : (x + y).fst = x.fst + y.fst := (rfl)
@[simp] private theorem snd_add (x y : TwistedAlg D) : (x + y).snd = x.snd + y.snd := (rfl)
@[simp] private theorem fst_mul (x y : TwistedAlg D) : (x * y).fst = x.fst * y.fst := (rfl)

@[simp]
private theorem snd_mul (x y : TwistedAlg D) :
    (x * y).snd = x.snd * y.fst +
      CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x.fst * y.snd :=
  (rfl)

private noncomputable instance : Ring (TwistedAlg D) where
  nsmul n x := ⟨n • x.fst, n • x.snd⟩
  zsmul n x := ⟨n • x.fst, n • x.snd⟩
  npow n x := npowRec n x
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  add_assoc x y z := TwistedAlg.ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add x := TwistedAlg.ext (zero_add _) (zero_add _)
  add_zero x := TwistedAlg.ext (add_zero _) (add_zero _)
  nsmul_zero x := TwistedAlg.ext (zero_smul ℕ _) (zero_smul ℕ _)
  nsmul_succ n x := TwistedAlg.ext (succ_nsmul _ _) (succ_nsmul _ _)
  zsmul_zero' x := TwistedAlg.ext (zero_smul ℤ _) (zero_smul ℤ _)
  zsmul_succ' n x := TwistedAlg.ext (SubNegMonoid.zsmul_succ' n _) (SubNegMonoid.zsmul_succ' n _)
  zsmul_neg' n x := TwistedAlg.ext (SubNegMonoid.zsmul_neg' n _) (SubNegMonoid.zsmul_neg' n _)
  sub_eq_add_neg x y := TwistedAlg.ext (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
  neg_add_cancel x := TwistedAlg.ext (neg_add_cancel _) (neg_add_cancel _)
  add_comm x y := TwistedAlg.ext (add_comm _ _) (add_comm _ _)
  mul_assoc x y z := TwistedAlg.ext (mul_assoc _ _ _) <| by
    simp only [snd_mul, fst_mul, map_mul, add_mul, mul_add, mul_assoc]
    abel
  one_mul x := TwistedAlg.ext (one_mul _) (by simp)
  mul_one x := TwistedAlg.ext (mul_one _) (by simp)
  zero_mul x := TwistedAlg.ext (zero_mul _) (by simp)
  mul_zero x := TwistedAlg.ext (mul_zero _) (by simp)
  left_distrib x y z := TwistedAlg.ext (mul_add _ _ _) <| by
    simp only [snd_mul, fst_add, snd_add, mul_add]
    abel
  right_distrib x y z := TwistedAlg.ext (add_mul _ _ _) <| by
    simp only [snd_mul, fst_add, snd_add, map_add, add_mul]
    abel

private noncomputable def toAlgebraRingHom (D : Derivation R A M) : A →+* TwistedAlg D where
  toFun a := ⟨algebraMap A _ a, ExteriorAlgebra.ι A (D a)⟩
  map_one' := TwistedAlg.ext (map_one _) (by simp)
  map_mul' a b := TwistedAlg.ext (map_mul _ a b) <| by
    simp only [snd_mul, D.leibniz, map_add, LinearMap.map_smul, CliffordAlgebra.involute.commutes,
      ← Algebra.smul_def]
    rw [← Algebra.commutes b (ExteriorAlgebra.ι A (D a)), ← Algebra.smul_def, add_comm]
  map_zero' := TwistedAlg.ext (map_zero _) (by simp)
  map_add' a b := TwistedAlg.ext (map_add _ a b) (by simp)

private noncomputable instance : Algebra A (TwistedAlg D) :=
  (toAlgebraRingHom D).toAlgebra' fun a x ↦ TwistedAlg.ext (Algebra.commutes a x.fst) <| by
    simp only [toAlgebraRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, snd_mul,
      CliffordAlgebra.involute.commutes, Algebra.commutes a x.snd,
      ExteriorAlgebra.ι_mul_eq_involute_mul]
    exact add_comm _ _

@[simp]
private theorem fst_algebraMap (a : A) :
    (algebraMap A (TwistedAlg D) a).fst = algebraMap A (ExteriorAlgebra A M) a :=
  (rfl)

@[simp]
private theorem snd_algebraMap (a : A) :
    (algebraMap A (TwistedAlg D) a).snd = ExteriorAlgebra.ι A (D a) :=
  (rfl)

end TwistedAlg

end TwistedAlgSection

section ExteriorDeriv

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

private theorem fst_lift_eq_id (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (m : M) : (u m).fst = m := by
  have h : TwistedExt.fstLinear D ∘ₗ u = LinearMap.id :=
    LinearMap.ext_on_range hspan fun a ↦ congrArg TwistedExt.fst (hu a)
  exact DFunLike.congr_fun h m

/-- `A`-algebra homomorphism `ExteriorAlgebra A M →ₐ[A] TwistedAlg D` whose first component is the
identity and whose second component is the exterior derivative. -/
private noncomputable def twistedLift (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a) :
    ExteriorAlgebra A M →ₐ[A] TwistedAlg D :=
  let L : M →ₗ[A] TwistedAlg D :=
    { toFun := fun m ↦ ⟨ExteriorAlgebra.ι A m, ((u m).snd : ExteriorAlgebra A M)⟩
      map_add' := fun m₁ m₂ ↦ TwistedAlg.ext (map_add _ m₁ m₂) <| by
        simp [u.map_add m₁ m₂]
      map_smul' := fun a m ↦ TwistedAlg.ext (by simp [Algebra.smul_def]) <| by
        change ((u (a • m)).snd : ExteriorAlgebra A M) =
          (algebraMap A (TwistedAlg D) a * ⟨ExteriorAlgebra.ι A m, (u m).snd⟩).snd
        rw [u.map_smul, TwistedExt.snd_smul, fst_lift_eq_id D u hspan hu m, Submodule.coe_add,
          SetLike.val_smul, TwistedExt.coe_ιMulti_two, TwistedAlg.snd_mul,
          TwistedAlg.snd_algebraMap, TwistedAlg.fst_algebraMap, CliffordAlgebra.involute.commutes,
          ← Algebra.smul_def] }
  have hsq : ∀ m, L m * L m = 0 := fun m ↦ TwistedAlg.ext (ExteriorAlgebra.ι_sq_zero m) <| by
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, TwistedAlg.snd_mul, CliffordAlgebra.involute_ι,
      neg_mul, TwistedAlg.snd_zero]
    rw [ExteriorAlgebra.ι_mul_eq_involute_mul m ((u m).snd : ExteriorAlgebra A M),
      TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower (u m).snd.2]
    simp
  ExteriorAlgebra.lift A ⟨L, hsq⟩

private theorem fst_twistedLift (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (x : ExteriorAlgebra A M) : (twistedLift D u hspan hu x).fst = x := by
  let fstHom : TwistedAlg D →+* ExteriorAlgebra A M :=
    { toFun := TwistedAlg.fst
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have h : fstHom.comp (twistedLift D u hspan hu).toRingHom =
      RingHom.id (ExteriorAlgebra A M) := by
    refine ExteriorAlgebra.ringHom_ext (fun a ↦ ?_) (fun m ↦ ?_)
    · exact congrArg TwistedAlg.fst ((twistedLift D u hspan hu).commutes a)
    · exact congrArg TwistedAlg.fst (ExteriorAlgebra.lift_ι_apply A _ _ m)
  exact RingHom.congr_fun h x

/-- **The graded exterior derivative on `ExteriorAlgebra A M`** associated to a derivation
`D : Derivation R A M` whose range spans `M` and an `A`-linear lift `u : M →ₗ[A] TwistedExt D`
of `D.derTwistedExt`. -/
noncomputable def exteriorAlgebraDeriv (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a) :
    ExteriorAlgebra A M →ₗ[R] ExteriorAlgebra A M where
  toFun x := (twistedLift D u hspan hu x).snd
  map_add' x y := congrArg TwistedAlg.snd (map_add (twistedLift D u hspan hu) x y)
  map_smul' r x := by
    have hmul : r • x = algebraMap A (ExteriorAlgebra A M) (algebraMap R A r) * x := by
      rw [← IsScalarTower.algebraMap_apply R A, Algebra.smul_def]
    have halg : (twistedLift D u hspan hu
        (algebraMap A (ExteriorAlgebra A M) (algebraMap R A r))).snd = 0 := by
      rw [(twistedLift D u hspan hu).commutes]
      simp
    rw [hmul, map_mul, TwistedAlg.snd_mul, halg, zero_mul, zero_add, fst_twistedLift,
      CliffordAlgebra.involute.commutes, ← IsScalarTower.algebraMap_apply R A, ← Algebra.smul_def]
    rfl

@[simp]
theorem exteriorAlgebraDeriv_algebraMap (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (a : A) :
    D.exteriorAlgebraDeriv u hspan hu (algebraMap A (ExteriorAlgebra A M) a) =
      ExteriorAlgebra.ι A (D a) :=
  congrArg TwistedAlg.snd ((twistedLift D u hspan hu).commutes a)

@[simp]
theorem exteriorAlgebraDeriv_one (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a) :
    D.exteriorAlgebraDeriv u hspan hu 1 = 0 :=
  congrArg TwistedAlg.snd (map_one (twistedLift D u hspan hu))

theorem exteriorAlgebraDeriv_ι (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (m : M) :
    D.exteriorAlgebraDeriv u hspan hu (ExteriorAlgebra.ι A m) =
      ((u m).snd : ExteriorAlgebra A M) :=
  congrArg TwistedAlg.snd (ExteriorAlgebra.lift_ι_apply A _ _ m)

@[simp]
theorem exteriorAlgebraDeriv_ι_apply (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (a : A) :
    D.exteriorAlgebraDeriv u hspan hu (ExteriorAlgebra.ι A (D a)) = 0 := by
  rw [exteriorAlgebraDeriv_ι, hu, snd_derTwistedExt, ZeroMemClass.coe_zero]

/-- **Graded Leibniz rule on `ExteriorAlgebra A M`.** -/
theorem exteriorAlgebraDeriv_mul (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (x y : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (x * y) =
      D.exteriorAlgebraDeriv u hspan hu x * y +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x *
          D.exteriorAlgebraDeriv u hspan hu y := by
  change (twistedLift D u hspan hu (x * y)).snd = _
  rw [map_mul, TwistedAlg.snd_mul, fst_twistedLift, fst_twistedLift]
  rfl

/-- Graded Leibniz rule when the left factor lies in `⋀[A]^p M`. -/
theorem exteriorAlgebraDeriv_mul_of_mem_exteriorPower (D : Derivation R A M)
    (u : M →ₗ[A] TwistedExt D) (hspan : Submodule.span A (Set.range D) = ⊤)
    (hu : ∀ a, u (D a) = D.derTwistedExt a) {p : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^p M) (y : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (x * y) =
      D.exteriorAlgebraDeriv u hspan hu x * y +
        (-1 : A) ^ p • (x * D.exteriorAlgebraDeriv u hspan hu y) := by
  rw [exteriorAlgebraDeriv_mul, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower hx,
    smul_mul_assoc]

theorem exteriorAlgebraDeriv_smul (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (a : A) (x : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (a • x) =
      ExteriorAlgebra.ι A (D a) * x + a • D.exteriorAlgebraDeriv u hspan hu x := by
  rw [Algebra.smul_def, exteriorAlgebraDeriv_mul, exteriorAlgebraDeriv_algebraMap,
    CliffordAlgebra.involute.commutes, ← Algebra.smul_def]

/-- The exterior derivative anticommutes with the grade involution on `ExteriorAlgebra A M`. -/
theorem exteriorAlgebraDeriv_involute (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (x : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu
        (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x) =
      -CliffordAlgebra.involute (Q := (0 : QuadraticForm A M))
        (D.exteriorAlgebraDeriv u hspan hu x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap a => simp
  | ι m =>
    change D.exteriorAlgebraDeriv u hspan hu
        (CliffordAlgebra.involute (ExteriorAlgebra.ι A m)) =
      -CliffordAlgebra.involute (D.exteriorAlgebraDeriv u hspan hu (ExteriorAlgebra.ι A m))
    rw [CliffordAlgebra.involute_ι, map_neg, exteriorAlgebraDeriv_ι,
      TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower (u m).snd.2]
    simp
  | mul x y hx hy =>
    rw [map_mul, exteriorAlgebraDeriv_mul, hx, hy, exteriorAlgebraDeriv_mul, map_add, map_mul,
      map_mul, neg_mul, mul_neg, neg_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]

/-- **Square-zero property (`d ∘ d = 0`) on `ExteriorAlgebra A M`.** -/
@[simp]
theorem exteriorAlgebraDeriv_exteriorAlgebraDeriv (D : Derivation R A M)
    (u : M →ₗ[A] TwistedExt D) (hspan : Submodule.span A (Set.range D) = ⊤)
    (hu : ∀ a, u (D a) = D.derTwistedExt a) (x : ExteriorAlgebra A M) :
    D.exteriorAlgebraDeriv u hspan hu (D.exteriorAlgebraDeriv u hspan hu x) = 0 := by
  have hmul : ∀ y z : ExteriorAlgebra A M,
      D.exteriorAlgebraDeriv u hspan hu (D.exteriorAlgebraDeriv u hspan hu (y * z)) =
        D.exteriorAlgebraDeriv u hspan hu (D.exteriorAlgebraDeriv u hspan hu y) * z +
          y * D.exteriorAlgebraDeriv u hspan hu (D.exteriorAlgebraDeriv u hspan hu z) := by
    intro y z
    rw [exteriorAlgebraDeriv_mul, map_add, exteriorAlgebraDeriv_mul, exteriorAlgebraDeriv_mul,
      exteriorAlgebraDeriv_involute, CliffordAlgebra.involute_involutive y, neg_mul]
    abel
  have hι : ∀ m : M,
      D.exteriorAlgebraDeriv u hspan hu
        (D.exteriorAlgebraDeriv u hspan hu (ExteriorAlgebra.ι A m)) = 0 := by
    let sqMap : M →ₗ[A] ExteriorAlgebra A M :=
      { toFun := fun m ↦ D.exteriorAlgebraDeriv u hspan hu
          (D.exteriorAlgebraDeriv u hspan hu (ExteriorAlgebra.ι A m))
        map_add' := fun m₁ m₂ ↦ by simp
        map_smul' := fun a m ↦ by
          rw [LinearMap.map_smul, Algebra.smul_def, hmul, exteriorAlgebraDeriv_algebraMap,
            exteriorAlgebraDeriv_ι_apply, zero_mul, zero_add, ← Algebra.smul_def,
            RingHom.id_apply] }
    have hsq : sqMap = 0 := LinearMap.ext_on_range hspan fun a ↦ by simp [sqMap]
    exact fun m ↦ DFunLike.congr_fun hsq m
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι m => exact hι m
  | mul y z hy hz => rw [hmul, hy, hz, zero_mul, mul_zero, add_zero]
  | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]

/-- **Uniqueness of the exterior derivative on `ExteriorAlgebra A M`.** Any `R`-linear graded
derivation sending `algebraMap a` to `ι (D a)` and annihilating `ι (D a)` equals
`D.exteriorAlgebraDeriv u hspan hu`. -/
theorem exteriorAlgebraDeriv_unique (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (δ' : ExteriorAlgebra A M →ₗ[R] ExteriorAlgebra A M)
    (halg : ∀ a, δ' (algebraMap A _ a) = ExteriorAlgebra.ι A (D a))
    (hd : ∀ a, δ' (ExteriorAlgebra.ι A (D a)) = 0)
    (hmul : ∀ x y, δ' (x * y) = δ' x * y +
      CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x * δ' y) :
    δ' = D.exteriorAlgebraDeriv u hspan hu := by
  suffices hdiff : ∀ x, (δ' - D.exteriorAlgebraDeriv u hspan hu) x = 0 by
    ext x
    exact sub_eq_zero.mp (hdiff x)
  have hdiff_alg : ∀ a, (δ' - D.exteriorAlgebraDeriv u hspan hu) (algebraMap A _ a) = 0 :=
    fun a ↦ by simp [halg]
  have hdiff_mul : ∀ x y,
      (δ' - D.exteriorAlgebraDeriv u hspan hu) (x * y) =
        (δ' - D.exteriorAlgebraDeriv u hspan hu) x * y +
          CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x *
            (δ' - D.exteriorAlgebraDeriv u hspan hu) y := fun x y ↦ by
    simp only [LinearMap.sub_apply, hmul, exteriorAlgebraDeriv_mul, sub_mul, mul_sub]
    abel
  have hdiff_ι : ∀ m : M,
      (δ' - D.exteriorAlgebraDeriv u hspan hu) (ExteriorAlgebra.ι A m) = 0 := by
    let diffMap : M →ₗ[A] ExteriorAlgebra A M :=
      { toFun := fun m ↦ (δ' - D.exteriorAlgebraDeriv u hspan hu) (ExteriorAlgebra.ι A m)
        map_add' := fun m₁ m₂ ↦ by simp only [map_add]
        map_smul' := fun a m ↦ by
          rw [LinearMap.map_smul, Algebra.smul_def, hdiff_mul, hdiff_alg, zero_mul, zero_add,
            CliffordAlgebra.involute.commutes, ← Algebra.smul_def, RingHom.id_apply] }
    have hzero : diffMap = 0 := LinearMap.ext_on_range hspan fun a ↦ by
      change (δ' - D.exteriorAlgebraDeriv u hspan hu) (ExteriorAlgebra.ι A (D a)) = 0
      rw [LinearMap.sub_apply, hd, exteriorAlgebraDeriv_ι_apply, sub_self]
    exact fun m ↦ DFunLike.congr_fun hzero m
  intro x
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => exact hdiff_alg a
  | ι m => exact hdiff_ι m
  | mul x y hx hy => rw [hdiff_mul, hx, hy, zero_mul, mul_zero, add_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- **Semilinear naturality of `exteriorAlgebraDeriv`.** -/
theorem mapSemilinear_exteriorAlgebraDeriv {B N : Type*} [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (D' : Derivation R B N) (u' : N →ₗ[B] TwistedExt D')
    (hspan' : Submodule.span B (Set.range D') = ⊤) (hu' : ∀ b, u' (D' b) = D'.derTwistedExt b)
    (f : A →ₐ[R] B) (g : M →ₛₗ[f.toRingHom] N) (hg : ∀ a, g (D a) = D' (f a))
    (x : ExteriorAlgebra A M) :
    ExteriorAlgebra.mapSemilinear g (D.exteriorAlgebraDeriv u hspan hu x) =
      D'.exteriorAlgebraDeriv u' hspan' hu' (ExteriorAlgebra.mapSemilinear g x) := by
  suffices h : ∀ z,
      ExteriorAlgebra.mapSemilinear g (D.exteriorAlgebraDeriv u hspan hu z) -
        D'.exteriorAlgebraDeriv u' hspan' hu' (ExteriorAlgebra.mapSemilinear g z) = 0 from
    sub_eq_zero.mp (h x)
  have halg : ∀ a : A,
      ExteriorAlgebra.mapSemilinear g
          (D.exteriorAlgebraDeriv u hspan hu (algebraMap A _ a)) -
        D'.exteriorAlgebraDeriv u' hspan' hu'
          (ExteriorAlgebra.mapSemilinear g (algebraMap A _ a)) = 0 := fun a ↦ by
    rw [exteriorAlgebraDeriv_algebraMap, ExteriorAlgebra.mapSemilinear_ι, hg,
      ExteriorAlgebra.mapSemilinear_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      exteriorAlgebraDeriv_algebraMap, sub_self]
  have hmul : ∀ y z : ExteriorAlgebra A M,
      ExteriorAlgebra.mapSemilinear g (D.exteriorAlgebraDeriv u hspan hu (y * z)) -
        D'.exteriorAlgebraDeriv u' hspan' hu' (ExteriorAlgebra.mapSemilinear g (y * z)) =
        (ExteriorAlgebra.mapSemilinear g (D.exteriorAlgebraDeriv u hspan hu y) -
            D'.exteriorAlgebraDeriv u' hspan' hu' (ExteriorAlgebra.mapSemilinear g y)) *
          ExteriorAlgebra.mapSemilinear g z +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm B N))
            (ExteriorAlgebra.mapSemilinear g y) *
          (ExteriorAlgebra.mapSemilinear g (D.exteriorAlgebraDeriv u hspan hu z) -
            D'.exteriorAlgebraDeriv u' hspan' hu' (ExteriorAlgebra.mapSemilinear g z)) :=
    fun y z ↦ by
      rw [exteriorAlgebraDeriv_mul, map_add, map_mul, map_mul,
        ExteriorAlgebra.mapSemilinear_involute, map_mul, exteriorAlgebraDeriv_mul, sub_mul,
        mul_sub]
      abel
  have hι : ∀ m : M,
      ExteriorAlgebra.mapSemilinear g
          (D.exteriorAlgebraDeriv u hspan hu (ExteriorAlgebra.ι A m)) -
        D'.exteriorAlgebraDeriv u' hspan' hu'
          (ExteriorAlgebra.mapSemilinear g (ExteriorAlgebra.ι A m)) = 0 := by
    intro m
    have hm : m ∈ Submodule.span A (Set.range D) := hspan ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨a, rfl⟩ := hm
      rw [exteriorAlgebraDeriv_ι_apply, map_zero, ExteriorAlgebra.mapSemilinear_ι, hg,
        exteriorAlgebraDeriv_ι_apply, sub_self]
    | zero => simp
    | add y z _ _ ihy ihz =>
      simp only [map_add]
      rw [add_sub_add_comm, ihy, ihz, add_zero]
    | smul a y _ ih =>
      rw [LinearMap.map_smul, Algebra.smul_def, hmul, halg, zero_mul, zero_add, ih, mul_zero]
  intro z
  induction z using ExteriorAlgebra.induction with
  | algebraMap a => exact halg a
  | ι m => exact hι m
  | mul y w ihy ihw => rw [hmul, ihy, ihw, zero_mul, mul_zero, add_zero]
  | add y w ihy ihw =>
    simp only [map_add]
    rw [add_sub_add_comm, ihy, ihw, add_zero]

/-- `exteriorAlgebraDeriv` raises exterior degree by `1`: it maps `⋀[A]^q M` into
`⋀[A]^(q + 1) M`. -/
theorem exteriorAlgebraDeriv_mem_exteriorPower (D : Derivation R A M)
    (u : M →ₗ[A] TwistedExt D) (hspan : Submodule.span A (Set.range D) = ⊤)
    (hu : ∀ a, u (D a) = D.derTwistedExt a) {q : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^q M) :
    D.exteriorAlgebraDeriv u hspan hu x ∈ ⋀[A]^(q + 1) M := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap a =>
    rw [exteriorAlgebraDeriv_algebraMap]
    exact TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one (D a)
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul w hw i x hx ih =>
    obtain ⟨m, rfl⟩ := hw
    rw [exteriorAlgebraDeriv_mul, exteriorAlgebraDeriv_ι, CliffordAlgebra.involute_ι, neg_mul]
    have h₁ : ((u m).snd : ExteriorAlgebra A M) * x ∈ ⋀[A]^(i + 1 + 1) M := by
      rw [show i + 1 + 1 = 2 + i by omega]
      exact SetLike.mul_mem_graded (u m).snd.2 hx
    exact add_mem h₁ (neg_mem (TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower m ih))

/-- **The `q`-th exterior derivative `⋀[A]^q M →ₗ[R] ⋀[A]^(q + 1) M`** associated to a derivation
`D : Derivation R A M` whose range spans `M` and an `A`-linear lift `u : M →ₗ[A] TwistedExt D`
of `D.derTwistedExt`. -/
noncomputable def exteriorDeriv (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (q : ℕ) : ⋀[A]^q M →ₗ[R] ⋀[A]^(q + 1) M where
  toFun ω := ⟨D.exteriorAlgebraDeriv u hspan hu ω.1,
    D.exteriorAlgebraDeriv_mem_exteriorPower u hspan hu ω.2⟩
  map_add' ω₁ ω₂ := Subtype.ext (map_add (D.exteriorAlgebraDeriv u hspan hu) ω₁.1 ω₂.1)
  map_smul' r ω := Subtype.ext ((D.exteriorAlgebraDeriv u hspan hu).map_smul r ω.1)

@[simp]
theorem coe_exteriorDeriv_apply (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (q : ℕ) (ω : ⋀[A]^q M) :
    (D.exteriorDeriv u hspan hu q ω : ExteriorAlgebra A M) =
      D.exteriorAlgebraDeriv u hspan hu ω.1 :=
  (rfl)

@[simp]
theorem exteriorDeriv_zero_symm (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (a : A) :
    D.exteriorDeriv u hspan hu 0 ((exteriorPower.zeroEquiv A M).symm a) =
      (exteriorPower.oneEquiv A M).symm (D a) := by
  apply Subtype.ext
  simp [exteriorPower.zeroEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_succ_apply,
    exteriorAlgebraDeriv_smul]

theorem oneEquiv_exteriorDeriv_zero (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (ω : ⋀[A]^0 M) :
    exteriorPower.oneEquiv A M (D.exteriorDeriv u hspan hu 0 ω) =
      D (exteriorPower.zeroEquiv A M ω) := by
  conv_lhs => rw [← (exteriorPower.zeroEquiv A M).symm_apply_apply ω, exteriorDeriv_zero_symm,
    LinearEquiv.apply_symm_apply]

@[simp]
theorem exteriorDeriv_exteriorDeriv_apply (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (q : ℕ) (ω : ⋀[A]^q M) :
    D.exteriorDeriv u hspan hu (q + 1) (D.exteriorDeriv u hspan hu q ω) = 0 :=
  Subtype.ext (D.exteriorAlgebraDeriv_exteriorAlgebraDeriv u hspan hu ω.1)

theorem exteriorDeriv_comp_exteriorDeriv (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (q : ℕ) :
    (D.exteriorDeriv u hspan hu (q + 1)) ∘ₗ (D.exteriorDeriv u hspan hu q) = 0 :=
  LinearMap.ext (D.exteriorDeriv_exteriorDeriv_apply u hspan hu q)

theorem exteriorDeriv_smul (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (q : ℕ) (a : A) (ω : ⋀[A]^q M) :
    D.exteriorDeriv u hspan hu q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D a) q ω + a • D.exteriorDeriv u hspan hu q ω := by
  apply Subtype.ext
  simpa using D.exteriorAlgebraDeriv_smul u hspan hu a ω.1

/-- The exterior derivative vanishes on pure wedge products of exact differentials `D bᵢ`. -/
@[simp]
theorem exteriorDeriv_ιMulti_comp_D (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    {q : ℕ} (b : Fin q → A) :
    D.exteriorDeriv u hspan hu q (exteriorPower.ιMulti A q (D ∘ b)) = 0 := by
  apply Subtype.ext
  rw [coe_exteriorDeriv_apply, exteriorPower.ιMulti_apply_coe, ZeroMemClass.coe_zero]
  induction q with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, Function.comp_apply, exteriorAlgebraDeriv_mul,
      exteriorAlgebraDeriv_ι_apply, zero_mul, zero_add]
    have htail : Matrix.vecTail (D ∘ b) = D ∘ Matrix.vecTail b := rfl
    rw [htail, ih (Matrix.vecTail b), mul_zero]

/-- **Formula on standard generators**:
`d(a • (D b₀ ∧ ⋯ ∧ D b_{q-1})) = D a ∧ D b₀ ∧ ⋯ ∧ D b_{q-1}`. -/
theorem exteriorDeriv_smul_ιMulti_comp_D (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    {q : ℕ} (a : A) (b : Fin q → A) :
    D.exteriorDeriv u hspan hu q (a • exteriorPower.ιMulti A q (D ∘ b)) =
      exteriorPower.ιMulti A (q + 1) (Fin.cons (D a) (D ∘ b)) := by
  rw [exteriorDeriv_smul, exteriorDeriv_ιMulti_comp_D, smul_zero, add_zero,
    TauCeti.ExteriorAlgebra.wedgeLeft_ιMulti]

/-- **Graded Leibniz rule on `exteriorPower.wedge`.** -/
theorem exteriorDeriv_wedge (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (p q : ℕ) (ω : ⋀[A]^p M) (η : ⋀[A]^q M) :
    D.exteriorDeriv u hspan hu (p + q) (exteriorPower.wedge A M p q ω η) =
      LinearEquiv.ofEq _ _ (congrArg (⋀[A]^· M) (Nat.add_right_comm p 1 q))
        (exteriorPower.wedge A M (p + 1) q (D.exteriorDeriv u hspan hu p ω) η) +
        (-1 : A) ^ p • exteriorPower.wedge A M p (q + 1) ω (D.exteriorDeriv u hspan hu q η) := by
  apply Subtype.ext
  simpa using D.exteriorAlgebraDeriv_mul_of_mem_exteriorPower u hspan hu ω.2 η.1

/-- **Semilinear naturality of `exteriorDeriv`.** -/
theorem mapSemilinear_exteriorDeriv {B N : Type*} [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (D : Derivation R A M) (u : M →ₗ[A] TwistedExt D)
    (hspan : Submodule.span A (Set.range D) = ⊤) (hu : ∀ a, u (D a) = D.derTwistedExt a)
    (D' : Derivation R B N) (u' : N →ₗ[B] TwistedExt D')
    (hspan' : Submodule.span B (Set.range D') = ⊤) (hu' : ∀ b, u' (D' b) = D'.derTwistedExt b)
    (f : A →ₐ[R] B) (g : M →ₛₗ[f.toRingHom] N) (hg : ∀ a, g (D a) = D' (f a))
    (q : ℕ) (ω : ⋀[A]^q M) :
    exteriorPower.mapSemilinear (q + 1) g (D.exteriorDeriv u hspan hu q ω) =
      D'.exteriorDeriv u' hspan' hu' q (exteriorPower.mapSemilinear q g ω) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_mapSemilinear_apply, coe_exteriorDeriv_apply]
  exact mapSemilinear_exteriorAlgebraDeriv D u hspan hu D' u' hspan' hu' f g hg ω.1

end ExteriorDeriv

end Derivation

/-! ### Algebraic exterior derivative on Kähler differentials -/

namespace KaehlerDifferential

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- **The algebraic exterior derivative on `ExteriorAlgebra A Ω[A⁄R]`.** -/
noncomputable def exteriorAlgebraDeriv :
    ExteriorAlgebra A Ω[A⁄R] →ₗ[R] ExteriorAlgebra A Ω[A⁄R] :=
  (D R A).exteriorAlgebraDeriv (D R A).derTwistedExt.liftKaehlerDifferential
    (span_range_derivation R A) (D R A).derTwistedExt.liftKaehlerDifferential_comp_D

/-- **The `q`-th algebraic exterior derivative `⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R]`.** -/
noncomputable def exteriorDeriv (q : ℕ) : ⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R] :=
  (D R A).exteriorDeriv (D R A).derTwistedExt.liftKaehlerDifferential
    (span_range_derivation R A) (D R A).derTwistedExt.liftKaehlerDifferential_comp_D q

variable {R A}

@[simp]
theorem coe_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (exteriorDeriv R A q ω : ExteriorAlgebra A Ω[A⁄R]) = exteriorAlgebraDeriv R A ω.1 :=
  (rfl)

@[simp]
theorem exteriorDeriv_zero_symm (a : A) :
    exteriorDeriv R A 0 ((exteriorPower.zeroEquiv A Ω[A⁄R]).symm a) =
      (exteriorPower.oneEquiv A Ω[A⁄R]).symm (D R A a) :=
  Derivation.exteriorDeriv_zero_symm _ _ _ _ a

@[simp]
theorem exteriorDeriv_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorDeriv R A (q + 1) (exteriorDeriv R A q ω) = 0 :=
  Derivation.exteriorDeriv_exteriorDeriv_apply _ _ _ _ q ω

theorem exteriorDeriv_smul (q : ℕ) (a : A) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorDeriv R A q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D R A a) q ω + a • exteriorDeriv R A q ω :=
  Derivation.exteriorDeriv_smul _ _ _ _ q a ω

@[simp]
theorem exteriorDeriv_ιMulti_comp_D {q : ℕ} (b : Fin q → A) :
    exteriorDeriv R A q (exteriorPower.ιMulti A q (D R A ∘ b)) = 0 :=
  Derivation.exteriorDeriv_ιMulti_comp_D _ _ _ _ b

theorem exteriorDeriv_smul_ιMulti_comp_D {q : ℕ} (a : A) (b : Fin q → A) :
    exteriorDeriv R A q (a • exteriorPower.ιMulti A q (D R A ∘ b)) =
      exteriorPower.ιMulti A (q + 1) (Fin.cons (D R A a) (D R A ∘ b)) :=
  Derivation.exteriorDeriv_smul_ιMulti_comp_D _ _ _ _ a b

/-- Universal naturality of `KaehlerDifferential.exteriorDeriv`: any derivation `D'` with a
twisted-extension lift `u'` receives a naturality identity along a semilinear map `g` sending
`D R A a` to `D' (f a)`. -/
theorem mapSemilinear_exteriorDeriv_of_derivation {B N : Type*} [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (D' : Derivation R B N) (u' : N →ₗ[B] Derivation.TwistedExt D')
    (hspan' : Submodule.span B (Set.range D') = ⊤) (hu' : ∀ b, u' (D' b) = D'.derTwistedExt b)
    (f : A →ₐ[R] B) (g : Ω[A⁄R] →ₛₗ[f.toRingHom] N) (hg : ∀ a, g (D R A a) = D' (f a))
    (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.mapSemilinear (q + 1) g (exteriorDeriv R A q ω) =
      D'.exteriorDeriv u' hspan' hu' q (exteriorPower.mapSemilinear q g ω) :=
  Derivation.mapSemilinear_exteriorDeriv _ _ _ _ D' u' hspan' hu' f g hg q ω

theorem mapSemilinear_exteriorDeriv {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.mapSemilinear (q + 1) (KaehlerDifferential.mapSemilinear f)
        (exteriorDeriv R A q ω) =
      exteriorDeriv R B q
        (exteriorPower.mapSemilinear q (KaehlerDifferential.mapSemilinear f) ω) :=
  mapSemilinear_exteriorDeriv_of_derivation _ _ _ _ f (KaehlerDifferential.mapSemilinear f)
    (KaehlerDifferential.mapSemilinear_D f) q ω

end KaehlerDifferential
