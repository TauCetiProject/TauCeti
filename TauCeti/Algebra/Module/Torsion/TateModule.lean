/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Tate modules of abelian groups

For an abelian group `A` and a prime `p`, its `p`-adic Tate module is the inverse limit

`TateModule p A = lim_n A[p^n]`

along the transition maps `A[p^(n+1)] → A[p^n]`, `x ↦ p • x`.  This file gives the inverse
limit a concrete carrier, its universal property, the inverse-limit topology, and its canonical
`ℤ_p`-module structure.  The action at level `n` is through reduction
`ℤ_p → ZMod (p ^ n)`.

The construction applies in particular to the point group of an elliptic curve.  Finite-level
torsion calculations can therefore be assembled into the `ℓ`-adic representation without
introducing an elliptic-curve-specific copy of the inverse-limit machinery.

## Main definitions

* `TauCeti.tateModuleSubgroup`: the subgroup of compatible `p`-power torsion families.
* `TauCeti.TateModule`: the `p`-adic Tate module, with its `ℤ_p`-module and inverse-limit
  topology.
* `TauCeti.TateModule.proj`: projection to `A[p^n]`.
* `TauCeti.TateModule.lift`: the map into the Tate module induced by compatible finite-level
  maps.
* `TauCeti.TateModule.mapLinearMap`: the `ℤ_p`-linear map induced by an additive homomorphism.

## Main results

* `TauCeti.TateModule.proj_succ`: consecutive components satisfy `p • x_(n+1) = x_n`.
* `TauCeti.TateModule.proj_smul`: projection is semilinear for reduction
  `ℤ_p → ZMod (p ^ n)`.
* `TauCeti.TateModule.continuous_iff`: a map into the Tate module is continuous exactly when
  all its finite-level components are locally constant.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.7.
-/

public section

noncomputable section

namespace TauCeti

variable (p : ℕ) (A : Type*) [AddCommGroup A]

/-- The `n`-th level `A[p^n]` of the `p`-power torsion tower. -/
abbrev TateModuleLevel (n : ℕ) : Type _ :=
  AddSubgroup.torsionBy A ((p ^ n : ℕ) : ℤ)

/-- The transition map `A[p^(n+1)] → A[p^n]`, given by multiplication by `p`. -/
def tateModuleTransition (n : ℕ) :
    TateModuleLevel p A (n + 1) →+ TateModuleLevel p A n where
  toFun x := ⟨p • (x : A), by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    rw [← mul_nsmul, ← pow_succ']
    simpa using congrArg Subtype.val (AddSubgroup.torsionBy.nsmul x)⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The transition map is multiplication by `p` on the underlying group. -/
@[simp]
theorem tateModuleTransition_apply (n : ℕ) (x : TateModuleLevel p A (n + 1)) :
    (tateModuleTransition p A n x : A) = p • (x : A) :=
  (rfl)

/-- The subgroup of the product of the groups `A[p^n]` consisting of families compatible under
multiplication by `p`. Its carrier is `TateModule p A`. -/
def tateModuleSubgroup : AddSubgroup (∀ n, TateModuleLevel p A n) where
  carrier := {x | ∀ n, tateModuleTransition p A n (x (n + 1)) = x n}
  zero_mem' n := by simp [tateModuleTransition]
  add_mem' {x y} hx hy n := by
    -- Membership in the subgroup unfolds to compatibility of the componentwise sum.
    change tateModuleTransition p A n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  neg_mem' {x} hx n := by
    -- Membership in the subgroup unfolds to compatibility of the componentwise negation.
    change tateModuleTransition p A n (-x (n + 1)) = -x n
    rw [map_neg, hx n]

variable {p A} in
/-- A family of `p`-power torsion points lies in the Tate module exactly when consecutive
components are compatible under multiplication by `p`. -/
theorem mem_tateModuleSubgroup_iff {x : ∀ n, TateModuleLevel p A n} :
    x ∈ tateModuleSubgroup p A ↔
      ∀ n, tateModuleTransition p A n (x (n + 1)) = x n :=
  Iff.rfl

/-- The `p`-adic Tate module of an abelian group: compatible families of `p^n`-torsion points. -/
def TateModule : Type _ :=
  tateModuleSubgroup p A

namespace TateModule

instance : AddCommGroup (TateModule p A) :=
  inferInstanceAs (AddCommGroup (tateModuleSubgroup p A))

variable {p A}

/-- Projection of the Tate module to its `p^n`-torsion level. -/
def proj (n : ℕ) : TateModule p A →+ TateModuleLevel p A n :=
  (Pi.evalAddMonoidHom (fun n ↦ TateModuleLevel p A n) n).comp
    (tateModuleSubgroup p A).subtype

/-- Consecutive components of a Tate-module point are compatible under multiplication by `p`. -/
@[simp]
theorem proj_succ (x : TateModule p A) (n : ℕ) :
    tateModuleTransition p A n (proj (n + 1) x) = proj n x :=
  -- Unfold `TateModule` to expose the compatible-family subtype carrying `x`.
  mem_tateModuleSubgroup_iff.1 (show tateModuleSubgroup p A from x).2 n

/-- A Tate-module point is determined by all of its finite-level components. -/
@[ext]
theorem ext {x y : TateModule p A} (h : ∀ n, proj n x = proj n y) : x = y :=
  Subtype.ext (funext h)

/-- The Tate-module point with prescribed compatible components. -/
def mk (x : ∀ n, TateModuleLevel p A n)
    (hx : ∀ n, tateModuleTransition p A n (x (n + 1)) = x n) : TateModule p A :=
  ⟨x, hx⟩

/-- The projection of a point constructed by `mk` is its prescribed component. -/
@[simp]
theorem proj_mk (x : ∀ n, TateModuleLevel p A n)
    (hx : ∀ n, tateModuleTransition p A n (x (n + 1)) = x n) (n : ℕ) :
    proj n (mk x hx) = x n :=
  (rfl)

/-- The family of projections identifies the Tate module with the subgroup of compatible
families in the product of the torsion levels. -/
theorem range_proj :
    Set.range (fun x : TateModule p A ↦ fun n ↦ proj n x) =
      (tateModuleSubgroup p A : Set (∀ n, TateModuleLevel p A n)) := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨mk x (mem_tateModuleSubgroup_iff.1 hx), funext fun _ ↦ rfl⟩⟩
  rintro ⟨y, rfl⟩
  exact fun n ↦ proj_succ y n

section Lift

variable {B : Type*} [AddZeroClass B]
  (f : ∀ n, B →+ TateModuleLevel p A n)
  (hf : ∀ n, (tateModuleTransition p A n).comp (f (n + 1)) = f n)

/-- The additive homomorphism into a Tate module determined by compatible finite-level maps. -/
def lift : B →+ TateModule p A :=
  (AddMonoidHom.pi f).codRestrict (tateModuleSubgroup p A) fun b n ↦
    DFunLike.congr_fun (hf n) b

/-- Projection after `lift` recovers the corresponding finite-level homomorphism. -/
@[simp]
theorem proj_lift (n : ℕ) : (proj n).comp (lift f hf) = f n :=
  (rfl)

/-- The lift of a compatible family of finite-level maps is unique. -/
theorem lift_unique (g : B →+ TateModule p A) (hg : ∀ n, (proj n).comp g = f n) :
    g = lift f hf :=
  AddMonoidHom.ext fun b ↦ ext fun n ↦ by
    exact (DFunLike.congr_fun (hg n) b).trans (congrArg (fun h ↦ h b) (proj_lift f hf n)).symm

end Lift

section Map

variable {B : Type*} [AddCommGroup B]

/-- The map on the `p^n`-torsion levels induced by an additive homomorphism. -/
def levelMap (f : A →+ B) (n : ℕ) : TateModuleLevel p A n →+ TateModuleLevel p B n :=
  (f.comp (AddSubgroup.torsionBy A ((p ^ n : ℕ) : ℤ)).subtype).codRestrict
    (AddSubgroup.torsionBy B ((p ^ n : ℕ) : ℤ)) fun x ↦ by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul]
      exact map_zero f

/-- The map induced on a torsion level agrees with the original homomorphism on underlying
elements. -/
@[simp]
theorem levelMap_apply (f : A →+ B) (n : ℕ) (x : TateModuleLevel p A n) :
    (levelMap f n x : B) = f x :=
  (rfl)

/-- An additive homomorphism induces an additive homomorphism of Tate modules, componentwise. -/
def map (f : A →+ B) : TateModule p A →+ TateModule p B :=
  (AddMonoidHom.pi fun n ↦ (levelMap (p := p) f n).comp (proj (p := p) n)).codRestrict
    (tateModuleSubgroup p B) fun x n ↦ by
      apply Subtype.ext
      -- Coercing both torsion levels to their ambient groups exposes naturality of `nsmul`.
      change p • f (proj (n + 1) x : A) = f (proj n x : A)
      rw [← map_nsmul]
      exact congrArg f (congrArg Subtype.val (proj_succ x n))

/-- The map induced on Tate modules is computed componentwise. -/
@[simp]
theorem proj_map (f : A →+ B) (x : TateModule p A) (n : ℕ) :
    proj n (map (p := p) f x) = levelMap (p := p) f n (proj n x) :=
  (rfl)

/-- Tate modules send identity homomorphisms to identity homomorphisms. -/
@[simp]
theorem map_id : map (p := p) (AddMonoidHom.id A) = AddMonoidHom.id (TateModule p A) := by
  ext x n
  rfl

/-- Tate modules send compositions to compositions. -/
@[simp]
theorem map_comp {C : Type*} [AddCommGroup C] (g : B →+ C) (f : A →+ B) :
    map (p := p) (g.comp f) = (map (p := p) g).comp (map (p := p) f) := by
  ext x n
  rfl

end Map

section PadicModule

variable [Fact p.Prime]

/-- The canonical module structure on the `p^n`-torsion level over `ZMod (p^n)`. -/
instance levelZModModule (n : ℕ) :
    Module (ZMod (p ^ n)) (TateModuleLevel p A n) :=
  AddSubgroup.torsionBy.zmodModule

private theorem transition_smul (n : ℕ) (a : ℤ_[p])
    (x : TateModuleLevel p A (n + 1)) :
    tateModuleTransition p A n (PadicInt.toZModPow (n + 1) a • x) =
      PadicInt.toZModPow n a • tateModuleTransition p A n x := by
  rw [← PadicInt.cast_toZModPow n (n + 1) n.le_succ a]
  let c := PadicInt.toZModPow (n + 1) a
  -- Replace the reduced p-adic scalar by `c` so its integer representative can be used below.
  rw [show PadicInt.toZModPow (n + 1) a = c from rfl]
  rw [← c.intCast_zmod_cast, Int.cast_smul_eq_zsmul, map_zsmul]
  rw [ZMod.cast_intCast (R := ZMod (p ^ n)) (pow_dvd_pow p n.le_succ),
    Int.cast_smul_eq_zsmul]

/-- Scalar multiplication by `ℤ_p`, obtained by reducing a scalar modulo `p^n` on the `n`-th
torsion level. -/
instance : SMul ℤ_[p] (TateModule p A) where
  smul a x := mk (fun n ↦ PadicInt.toZModPow n a • proj n x) fun n ↦ by
    rw [transition_smul, proj_succ]

/-- Scalar multiplication on the `n`-th projection is reduction modulo `p^n`. -/
@[simp]
theorem proj_smul (a : ℤ_[p]) (x : TateModule p A) (n : ℕ) :
    proj n (a • x) = PadicInt.toZModPow n a • proj n x :=
  (rfl)

/-- The Tate module is canonically a module over the `p`-adic integers. -/
instance : Module ℤ_[p] (TateModule p A) where
  one_smul x := ext fun n ↦ by simp
  mul_smul a b x := ext fun n ↦ by simp [mul_smul]
  smul_zero a := ext fun n ↦ by simp
  smul_add a x y := ext fun n ↦ by simp [smul_add]
  add_smul a b x := ext fun n ↦ by simp [add_smul]
  zero_smul x := ext fun n ↦ by simp

section Map

variable {B : Type*} [AddCommGroup B]

/-- An additive homomorphism induces a `ℤ_p`-linear map on Tate modules. -/
def mapLinearMap (f : A →+ B) : TateModule p A →ₗ[ℤ_[p]] TateModule p B where
  toAddHom := map (p := p) f
  map_smul' a x := by
    apply ext
    intro n
    exact ZMod.map_smul (levelMap (p := p) f n) (PadicInt.toZModPow n a) (proj n x)

/-- The linear map induced on Tate modules has the same underlying additive map as `map`. -/
@[simp]
theorem mapLinearMap_apply (f : A →+ B) (x : TateModule p A) : mapLinearMap f x = map f x :=
  (rfl)

end Map

end PadicModule

/-! ### The inverse-limit topology -/

/-- The inverse-limit topology, induced from the product of the discrete torsion levels. -/
instance : TopologicalSpace (TateModule p A) :=
  .induced (fun x n ↦ proj n x) (@Pi.topologicalSpace _ _ fun _ ↦ ⊥)

private theorem isInducing_proj
    [t : ∀ n, TopologicalSpace (TateModuleLevel p A n)]
    [∀ n, DiscreteTopology (TateModuleLevel p A n)] :
    Topology.IsInducing (fun x : TateModule p A ↦ fun n ↦ proj n x) := by
  refine ⟨?_⟩
  -- Every supplied level topology is discrete, hence equal to the bottom topology used above.
  rw [show t = fun _ ↦ ⊥ from funext fun n ↦ DiscreteTopology.eq_bot]
  rfl

/-- A map into a Tate module is continuous exactly when all its finite-level components are
locally constant. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → TateModule p A} :
    Continuous f ↔ ∀ n, IsLocallyConstant fun x ↦ proj n (f x) := by
  let (n : ℕ) : TopologicalSpace (TateModuleLevel p A n) := ⊥
  have (n : ℕ) : DiscreteTopology (TateModuleLevel p A n) := ⟨rfl⟩
  simp_rw [isInducing_proj.continuous_iff, continuous_pi_iff, IsLocallyConstant.iff_continuous,
    Function.comp_def]

/-- Every finite-level projection is locally constant. -/
theorem isLocallyConstant_proj (n : ℕ) :
    IsLocallyConstant (proj n : TateModule p A → TateModuleLevel p A n) :=
  continuous_iff.1 continuous_id n

instance : IsTopologicalAddGroup (TateModule p A) :=
  letI (n : ℕ) : TopologicalSpace (TateModuleLevel p A n) := ⊥
  haveI (n : ℕ) : DiscreteTopology (TateModuleLevel p A n) := ⟨rfl⟩
  isInducing_proj.isTopologicalAddGroup (AddMonoidHom.pi proj)

/-- The canonical action of the `p`-adic integers on the Tate module is jointly continuous. -/
instance [Fact p.Prime] : ContinuousSMul ℤ_[p] (TateModule p A) where
  continuous_smul := continuous_iff.2 fun n ↦ by
    have ha : IsLocallyConstant (fun x : ℤ_[p] × TateModule p A ↦
        PadicInt.toZModPow n x.1) :=
      (IsLocallyConstant.iff_continuous _).2
        ((PadicInt.continuous_toZModPow n).comp continuous_fst)
    have hx : IsLocallyConstant (fun x : ℤ_[p] × TateModule p A ↦ proj n x.2) :=
      (isLocallyConstant_proj n).comp_continuous continuous_snd
    simpa only [proj_smul] using ha.comp₂ hx (fun a x ↦ a • x)

private theorem isEmbedding_proj
    [∀ n, TopologicalSpace (TateModuleLevel p A n)]
    [∀ n, DiscreteTopology (TateModuleLevel p A n)] :
    Topology.IsEmbedding (fun x : TateModule p A ↦ fun n ↦ proj n x) :=
  ⟨isInducing_proj, fun _ _ h ↦ ext (congrFun h)⟩

instance : T2Space (TateModule p A) :=
  letI (n : ℕ) : TopologicalSpace (TateModuleLevel p A n) := ⊥
  haveI (n : ℕ) : DiscreteTopology (TateModuleLevel p A n) := ⟨rfl⟩
  isEmbedding_proj.t2Space

instance : TotallyDisconnectedSpace (TateModule p A) :=
  letI (n : ℕ) : TopologicalSpace (TateModuleLevel p A n) := ⊥
  haveI (n : ℕ) : DiscreteTopology (TateModuleLevel p A n) := ⟨rfl⟩
  isEmbedding_proj.isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- If all `p`-power torsion levels are finite, then the Tate module is compact. -/
instance [∀ n, Finite (TateModuleLevel p A n)] : CompactSpace (TateModule p A) := by
  let (n : ℕ) : TopologicalSpace (TateModuleLevel p A n) := ⊥
  have (n : ℕ) : DiscreteTopology (TateModuleLevel p A n) := ⟨rfl⟩
  refine Topology.IsClosedEmbedding.compactSpace
    (f := fun x : TateModule p A ↦ fun n ↦ proj n x) ⟨isEmbedding_proj, ?_⟩
  rw [range_proj]
  simp only [tateModuleSubgroup, AddSubgroup.coe_set_mk, AddSubmonoid.coe_set_mk,
    Set.ofPred_forall]
  exact isClosed_iInter fun n ↦ isClosed_eq
    (continuous_of_discreteTopology.comp (continuous_apply (n + 1)))
    (continuous_apply n)

/-- The homomorphism on Tate modules induced by an additive homomorphism is continuous. -/
theorem continuous_map {B : Type*} [AddCommGroup B] (f : A →+ B) :
    Continuous (map (p := p) f : TateModule p A → TateModule p B) := by
  refine continuous_iff.2 fun n ↦ ?_
  -- Unfold the component formula `proj_map` as a composition with the source projection.
  change IsLocallyConstant
    ((levelMap (p := p) f n : TateModuleLevel p A n → TateModuleLevel p B n) ∘ proj n)
  exact (isLocallyConstant_proj (p := p) (A := A) n).comp (levelMap (p := p) f n)

end TateModule

end TauCeti

end
