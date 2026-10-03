/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.Finiteness
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
* `TauCeti.TateModule.continuous_map_apply`: a family of homomorphisms moving each torsion point
  locally constantly acts jointly continuously on Tate modules.
* `TauCeti.TateModule.proj_surjective`: if the transition maps are surjective, so is every
  projection.
* `TauCeti.TateModule.nonempty_linearEquiv_of_natCard`: if `A[p^n]` has `(p^n)^r` elements for
  every `n`, then `T_p A ≃ ℤ_p^r`; hence `T_p A` is free of rank `r`
  (`TauCeti.TateModule.free_of_natCard`, `TauCeti.TateModule.finrank_eq_of_natCard`).

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

/-- **Homomorphisms moving torsion locally constantly act continuously on Tate modules.** If
`f : G → (A →+ B)` is a family of homomorphisms parametrised by a topological space `G`, and
`g ↦ f g x` is locally constant for every `p`-power torsion point `x`, then
`(g, y) ↦ map (f g) y` is jointly continuous. This is how a profinite Galois group acting on the
torsion points of `A` acts continuously on `T_p A`. -/
theorem continuous_map_apply {G : Type*} [TopologicalSpace G] {B : Type*} [AddCommGroup B]
    {f : G → A →+ B} (hf : ∀ n (x : TateModuleLevel p A n), IsLocallyConstant fun g ↦ f g x) :
    Continuous fun q : G × TateModule p A ↦ map (p := p) (f q.1) q.2 := by
  refine continuous_iff.2 fun n ↦ (IsLocallyConstant.iff_eventually_eq _).2 fun q₀ ↦ ?_
  have hg := (continuous_fst.tendsto q₀).eventually
    ((IsLocallyConstant.iff_eventually_eq _).1 (hf n (proj n q₀.2)) q₀.1)
  have hy := (continuous_snd.tendsto q₀).eventually
    ((IsLocallyConstant.iff_eventually_eq _).1 (isLocallyConstant_proj (p := p) (A := A) n) q₀.2)
  filter_upwards [hg, hy] with q hgq hyq
  rw [proj_map, proj_map, hyq]
  exact Subtype.ext hgq

/-! ### Freeness -/

section Free

/-- The components of a Tate-module point satisfy `x_m = p ^ k • x_(m + k)`. -/
theorem coe_proj_eq_pow_nsmul (x : TateModule p A) (m k : ℕ) :
    (proj m x : A) = p ^ k • (proj (m + k) x : A) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := congrArg Subtype.val (proj_succ x (m + k))
    rw [tateModuleTransition_apply] at h
    rw [ih, ← h, ← mul_nsmul', ← pow_succ, add_assoc]

/-- The components of a Tate-module point satisfy `x_m = p ^ (n - m) • x_n` for `m ≤ n`. -/
theorem coe_proj_eq_pow_sub_nsmul (x : TateModule p A) {m n : ℕ} (h : m ≤ n) :
    (proj m x : A) = p ^ (n - m) • (proj n x : A) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, coe_proj_eq_pow_nsmul]

/-- If every transition map is surjective, then every point of every torsion level is a component
of a Tate-module point. -/
theorem proj_surjective (h : ∀ n, Function.Surjective (tateModuleTransition p A n)) (n : ℕ) :
    Function.Surjective (proj (p := p) (A := A) n) := by
  intro x
  choose g hg using h
  -- `t k` is a lift of `x` to the level `n + k`, so `p ^ n • t k` is a lift to level `k`.
  let t : ∀ k, TateModuleLevel p A (n + k) := fun k ↦
    Nat.rec (motive := fun k ↦ TateModuleLevel p A (n + k)) x (fun k y ↦ g (n + k) y) k
  have ht (k : ℕ) : p • (t (k + 1) : A) = t k := by
    simpa using congrArg Subtype.val (hg (n + k) (t k))
  have hx (k : ℕ) : p ^ k • (t k : A) = x := by
    induction k with
    | zero => simp [t]
    | succ k ih => rw [pow_succ, mul_nsmul', ht, ih]
  refine ⟨mk (fun m ↦ ⟨p ^ n • (t m : A), ?_⟩) fun m ↦ ?_, ?_⟩
  · rw [AddSubgroup.torsionBy.nsmul_iff, smul_smul, ← pow_add, add_comm]
    exact AddSubgroup.torsionBy.nsmul_iff.mp (t m).2
  · ext
    simp [smul_comm p (p ^ n), ht]
  · ext
    simpa using hx n

/-- If the `p ^ n`-torsion has `(p ^ n) ^ r` elements for every `n`, then multiplication by `p`
maps `A[p ^ (n + 1)]` onto `A[p ^ n]`. -/
theorem tateModuleTransition_surjective_of_natCard {r : ℕ} (hp : p ≠ 0)
    (hcard : ∀ n, Nat.card (TateModuleLevel p A n) = (p ^ n) ^ r) (n : ℕ) :
    Function.Surjective (tateModuleTransition p A n) := by
  have hfin (k : ℕ) : Finite (TateModuleLevel p A k) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  set f := tateModuleTransition p A n
  have hker : Nat.card f.ker ≤ p ^ r := by
    have hinj : Function.Injective (fun x : f.ker ↦
        (⟨((x : TateModuleLevel p A (n + 1)) : A), by
          rw [AddSubgroup.torsionBy.nsmul_iff, pow_one]
          simpa [f] using congrArg Subtype.val x.2⟩ : TateModuleLevel p A 1)) :=
      fun x y hxy ↦ Subtype.ext (Subtype.ext (congrArg Subtype.val hxy :))
    exact (Nat.card_le_card_of_injective _ hinj).trans_eq (by rw [hcard 1, pow_one])
  have hrange : Nat.card f.range = Nat.card (TateModuleLevel p A n) := by
    refine le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective) ?_
    have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, hcard] at h
    rw [hcard]
    refine Nat.le_of_mul_le_mul_right (c := p ^ r) ?_ (by positivity)
    rw [← mul_pow, ← pow_succ, h]
    exact Nat.mul_le_mul_left _ hker
  exact AddMonoidHom.range_eq_top.mp (AddSubgroup.eq_top_of_card_eq _ hrange)

variable {ι : Type*} [Fintype ι] {e : ι → TateModule p A}

/-- If the level-one components of `e` admit no integer relation that is nontrivial modulo `p`,
then every integer relation among its level-`n` components is divisible by `p ^ n`. -/
private theorem pow_dvd_of_sum_zsmul_eq_zero
    (he : ∀ c : ι → ℤ, ∑ i, c i • (proj 1 (e i) : A) = 0 → ∀ i, (p : ℤ) ∣ c i) (n : ℕ) :
    ∀ c : ι → ℤ, ∑ i, c i • (proj n (e i) : A) = 0 → ∀ i, (p : ℤ) ^ n ∣ c i := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro c hc
    have h1 : ∑ i, c i • (proj 1 (e i) : A) = 0 := by
      have (i : ι) : (proj 1 (e i) : A) = p ^ n • (proj (n + 1) (e i) : A) := by
        rw [coe_proj_eq_pow_sub_nsmul (e i) (by omega : 1 ≤ n + 1), Nat.add_sub_cancel]
      simp_rw [this, smul_comm (c _) (p ^ n), ← Finset.smul_sum, hc, smul_zero]
    choose d hd using he c h1
    have h2 : ∑ i, d i • (proj n (e i) : A) = 0 := by
      have (i : ι) : (proj n (e i) : A) = p • (proj (n + 1) (e i) : A) := by
        rw [coe_proj_eq_pow_sub_nsmul (e i) (by omega : n ≤ n + 1), Nat.add_sub_cancel_left,
          pow_one]
      simp_rw [this, ← natCast_zsmul, smul_smul, mul_comm (d _), ← hd, hc]
    intro i
    rw [hd i, pow_succ']
    exact mul_dvd_mul_left _ (ih d h2 i)

/-- The `ZMod (p ^ n)`-action on the `n`-th torsion level is multiplication by a representative. -/
theorem coe_zmod_smul [NeZero p] {n : ℕ} (z : ZMod (p ^ n)) (y : TateModuleLevel p A n) :
    ((z • y : TateModuleLevel p A n) : A) = z.val • (y : A) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.coe_nsmul _ _ _

variable [hp : Fact p.Prime]

/-- Under the hypothesis of `pow_dvd_of_sum_zsmul_eq_zero`, the level-`n` components of `e` are
linearly independent over `ZMod (p ^ n)`. -/
private theorem eq_zero_of_sum_smul_proj_eq_zero
    (he : ∀ c : ι → ℤ, ∑ i, c i • (proj 1 (e i) : A) = 0 → ∀ i, (p : ℤ) ∣ c i) {n : ℕ}
    {c : ι → ZMod (p ^ n)} (hc : ∑ i, c i • proj n (e i) = 0) : c = 0 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hc' : ∑ i, (c i).val • (proj n (e i) : A) = 0 := by
    simpa [coe_zmod_smul] using congrArg Subtype.val hc
  funext i
  rw [Pi.zero_apply, ← ZMod.natCast_zmod_val (c i), ZMod.natCast_eq_zero_iff,
    ← Int.natCast_dvd_natCast]
  exact_mod_cast pow_dvd_of_sum_zsmul_eq_zero he n (fun i ↦ ((c i).val : ℤ))
    (by simpa only [natCast_zsmul] using hc') i

variable {r : ℕ} (hcard : ∀ n, Nat.card (TateModuleLevel p A n) = (p ^ n) ^ r)
include hcard

/-- Lifting a `ZMod p`-basis of the first level gives `r` points of the Tate module whose
level-one components admit no integer relation that is nontrivial modulo `p`. -/
private theorem exists_independent_of_natCard :
    ∃ e : Fin r → TateModule p A,
      ∀ c : Fin r → ℤ, ∑ i, c i • (proj 1 (e i) : A) = 0 → ∀ i, (p : ℤ) ∣ c i := by
  -- The first level is a vector space of dimension `r` over `ZMod p`; take a basis `b` of it.
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp1 (x : TateModuleLevel p A 1) : p • x = 0 := by
    simpa using AddSubgroup.torsionBy.nsmul x
  have : Module (ZMod p) (TateModuleLevel p A 1) := AddCommMonoid.zmodModule hp1
  have : Finite (TateModuleLevel p A 1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (NeZero.ne _))
  have : Module.Finite (ZMod p) (TateModuleLevel p A 1) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod p) (TateModuleLevel p A 1) = r := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TateModuleLevel p A 1)
    rw [hcard, ← pow_mul, one_mul, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) (TateModuleLevel p A 1) hrank
  have hb (c : Fin r → ℤ) (hc : ∑ i, c i • b i = 0) (i : Fin r) : (p : ℤ) ∣ c i := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    refine Fintype.linearIndependent_iff.mp b.linearIndependent (fun i ↦ (c i : ZMod p)) ?_ i
    simpa [Int.cast_smul_eq_zsmul] using hc
  -- Lift the basis to the Tate module.
  choose e he using fun i ↦
    proj_surjective (tateModuleTransition_surjective_of_natCard hp.out.ne_zero hcard) 1 (b i)
  exact ⟨e, fun c hc i ↦ hb c (Subtype.ext (by simpa [he] using hc)) i⟩

/-- At each level, the components of such points form a `ZMod (p ^ n)`-basis. -/
private theorem bijective_sum_smul_proj {e : Fin r → TateModule p A}
    (he : ∀ c : Fin r → ℤ, ∑ i, c i • (proj 1 (e i) : A) = 0 → ∀ i, (p : ℤ) ∣ c i) (n : ℕ) :
    Function.Bijective fun c : Fin r → ZMod (p ^ n) ↦ ∑ i, c i • proj n (e i) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : Finite (TateModuleLevel p A n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (NeZero.ne _))
  refine Function.Injective.bijective_of_nat_card_le (fun c d hcd ↦ ?_) ?_
  · refine sub_eq_zero.mp (eq_zero_of_sum_smul_proj_eq_zero he ?_)
    simpa [sub_smul, Finset.sum_sub_distrib, sub_eq_zero] using hcd
  · rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The points constructed by `exists_independent_of_natCard` generate the Tate module over
`ℤ_p`. -/
private theorem linearCombination_surjective {e : Fin r → TateModule p A}
    (he : ∀ c : Fin r → ℤ, ∑ i, c i • (proj 1 (e i) : A) = 0 → ∀ i, (p : ℤ) ∣ c i) :
    Function.Surjective (Fintype.linearCombination ℤ_[p] e) := by
  intro x
  choose c hc using fun n ↦ (bijective_sum_smul_proj hcard he n).2 (proj n x)
  have hA (n : ℕ) : ∑ i, (c n i).val • (proj n (e i) : A) = proj n x := by
    simpa [coe_zmod_smul] using congrArg Subtype.val (hc n)
  have hA' {m n : ℕ} (h : m ≤ n) : ∑ i, (c n i).val • (proj m (e i) : A) = proj m x := by
    simp_rw [coe_proj_eq_pow_sub_nsmul _ h, smul_comm _ (p ^ (n - m)), ← Finset.smul_sum, hA]
  have hI (k : ℕ) (y : ℤ_[p]) :
      y ∈ (IsLocalRing.maximalIdeal ℤ_[p] ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p]) ↔
        (p : ℤ_[p]) ^ k ∣ y := by
    rw [smul_eq_mul, Ideal.mul_top, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  -- The integer coefficients at the successive levels form a `p`-adic Cauchy sequence.
  choose a ha using fun i ↦ IsPrecomplete.prec (I := IsLocalRing.maximalIdeal ℤ_[p])
    inferInstance (f := fun n ↦ (((c n i).val : ℤ) : ℤ_[p])) fun {m n} h ↦ by
      have hd : (p : ℤ) ^ m ∣ (c m i).val - (c n i).val := by
        rw [← dvd_neg, neg_sub]
        exact pow_dvd_of_sum_zsmul_eq_zero he m (fun j ↦ ((c n j).val : ℤ) - (c m j).val) (by
          simp_rw [sub_smul, Finset.sum_sub_distrib, natCast_zsmul, hA' h, hA m, sub_self]) i
      rw [SModEq.sub_mem, hI]
      simpa using (Int.castRingHom ℤ_[p]).map_dvd hd
  refine ⟨a, ext fun n ↦ ?_⟩
  rw [Fintype.linearCombination_apply, map_sum, ← hc n]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [proj_smul]
  congr 1
  have h := (hI n _).mp (SModEq.sub_mem.mp (ha i n))
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero] at h
  rw [← h, map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **A Tate module whose `p ^ n`-torsion levels have `(p ^ n) ^ r` elements is free of rank
`r`**: it is isomorphic to `ℤ_p ^ r`. The isomorphism is noncanonical, so the result asserts its
existence. -/
theorem nonempty_linearEquiv_of_natCard :
    Nonempty (TateModule p A ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) := by
  obtain ⟨e, he⟩ := exists_independent_of_natCard hcard
  refine ⟨(LinearEquiv.ofBijective (Fintype.linearCombination ℤ_[p] e)
    ⟨fun a a' h ↦ funext fun i ↦ ?_, linearCombination_surjective hcard he⟩).symm⟩
  refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
  have h' : (fun i ↦ PadicInt.toZModPow n (a i)) = fun i ↦ PadicInt.toZModPow n (a' i) :=
    (bijective_sum_smul_proj hcard he n).1 <| by
      simpa [Fintype.linearCombination_apply] using congrArg (proj n) h
  exact congrFun h' i

/-- A Tate module whose `p ^ n`-torsion levels have `(p ^ n) ^ r` elements is free over `ℤ_p`. -/
theorem free_of_natCard : Module.Free ℤ_[p] (TateModule p A) :=
  Module.Free.of_equiv (nonempty_linearEquiv_of_natCard hcard).some.symm

/-- A Tate module whose `p ^ n`-torsion levels have `(p ^ n) ^ r` elements is finitely generated
over `ℤ_p`. -/
theorem finite_of_natCard : Module.Finite ℤ_[p] (TateModule p A) :=
  Module.Finite.equiv (nonempty_linearEquiv_of_natCard hcard).some.symm

/-- A Tate module whose `p ^ n`-torsion levels have `(p ^ n) ^ r` elements has rank `r` over
`ℤ_p`. -/
theorem finrank_eq_of_natCard : Module.finrank ℤ_[p] (TateModule p A) = r := by
  rw [(nonempty_linearEquiv_of_natCard hcard).some.finrank_eq, Module.finrank_fin_fun]

end Free

end TateModule

end TauCeti

end
