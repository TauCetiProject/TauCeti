/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Homotopy.Path
public import TauCeti.Topology.Connected.PathComponentOne

/-!
# The group of homotopy classes of maps into a topological group

Let `G` be a topological group and `X` a topological space. Pointwise multiplication of maps
`X → G` is compatible with homotopy (`ContinuousMap.Homotopic.mul`, `ContinuousMap.Homotopic.inv`),
so the maps homotopic to the constant map `1` form a normal subgroup of `C(X, G)`
(`ContinuousMap.homotopicOneSubgroup`). The quotient is the group `[X, G]` of free homotopy classes
of maps `X → G` under pointwise multiplication (`TauCeti.HomotopyClassGroup`): two maps have the
same class exactly when they are homotopic (`TauCeti.HomotopyClassGroup.mk_eq_mk_iff`).

Write `π₀(G)` for the quotient `G ⧸ G₀` of `G` by the path component of the identity
(`Subgroup.pathComponentOne`). For a point `q` of `X`, evaluation at `q` induces a homomorphism
`[X, G] →* π₀(G)` (`TauCeti.HomotopyClassGroup.eval`), and constant maps induce a homomorphism
`π₀(G) →* [X, G]` (`TauCeti.HomotopyClassGroup.const`) splitting it
(`TauCeti.HomotopyClassGroup.eval_const`). Its kernel consists of the classes of maps sending `q`
to `1` (`TauCeti.HomotopyClassGroup.mem_ker_eval_iff`): a map `f` with `f q` in the identity
component is homotopic to the based map `x ↦ f x * (f q)⁻¹`.

Two maps into `G` agreeing at `q` and freely homotopic are homotopic relative to `q`
(`ContinuousMap.homotopicRel_singleton_iff_homotopic_of_apply_eq`): a free homotopy `H` is corrected
to `(t, x) ↦ H (t, x) * (H (t, q))⁻¹ * f q`. So classes of based maps in `[X, G]` are exactly their
pointed homotopy classes (`TauCeti.HomotopyClassGroup.mk_eq_mk_iff_homotopicRel`). For a sphere
these are the based homotopy classes forming `πₙ(G, 1)`, and `[Sⁿ, G]` is an extension of `π₀(G)`
by `πₙ(G, 1)`; this is in `TauCeti.Topology.Homotopy.HomotopyClassGroup.Sphere`.

For a discrete space `X`, a map `X → G` is any function, and a homotopy is any family of paths, so
`[X, G]` is the product `X → π₀(G)` (`TauCeti.HomotopyClassGroup.piMulEquivOfDiscrete`).

## Main definitions

* `ContinuousMap.Homotopy.mul`, `ContinuousMap.Homotopy.inv`: pointwise products and inverses of
  homotopies, for a continuous multiplication or inversion on the target.
* `ContinuousMap.homotopicOneSubgroup X G`: the normal subgroup of maps homotopic to `1`.
* `TauCeti.HomotopyClassGroup X G`: the group `[X, G]` of free homotopy classes of maps `X → G`.
* `TauCeti.HomotopyClassGroup.eval G q : [X, G] →* π₀(G)`: evaluation at `q`.
* `TauCeti.HomotopyClassGroup.const X : π₀(G) →* [X, G]`: classes of constant maps.

## Main results

* `TauCeti.HomotopyClassGroup.mk_eq_mk_iff`: maps have the same class iff they are homotopic.
* `ContinuousMap.homotopicRel_singleton_iff_homotopic_of_apply_eq`: maps into a topological group
  agreeing at `q` are homotopic relative to `q` iff they are homotopic.
* `TauCeti.HomotopyClassGroup.eval_const`, `TauCeti.HomotopyClassGroup.eval_surjective`: evaluation
  is split by constant maps.
* `TauCeti.HomotopyClassGroup.mem_ker_eval_iff`: the kernel of evaluation at `q` consists of the
  classes of maps sending `q` to `1`.
* `TauCeti.HomotopyClassGroup.piMulEquivOfDiscrete`: `[X, G] ≃* (X → π₀(G))` for discrete `X`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Graduate Texts in Mathematics 61, Springer
  (1978), Chapter III, §5 (homotopy classes of maps into a topological group).
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2 (clutching functions and `[Sⁿ, G]`).
-/

public section

open scoped unitInterval

namespace ContinuousMap

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]

section Mul

variable [Mul G] [ContinuousMul G] {f₀ f₁ g₀ g₁ : C(X, G)}

/-- The pointwise product `(t, x) ↦ F (t, x) * H (t, x)` of homotopies `F : f₀ ≃ f₁` and
`H : g₀ ≃ g₁` of maps into a space with a continuous multiplication, a homotopy
`f₀ * g₀ ≃ f₁ * g₁`. -/
@[to_additive /-- The pointwise sum `(t, x) ↦ F (t, x) + H (t, x)` of homotopies `F : f₀ ≃ f₁`
and `H : g₀ ≃ g₁` of maps into a space with a continuous addition, a homotopy
`f₀ + g₀ ≃ f₁ + g₁`. -/]
def Homotopy.mul (F : Homotopy f₀ f₁) (H : Homotopy g₀ g₁) : Homotopy (f₀ * g₀) (f₁ * g₁) where
  toFun x := F x * H x
  continuous_toFun := F.continuous.mul H.continuous
  map_zero_left x := by simp
  map_one_left x := by simp

@[to_additive (attr := simp)]
theorem Homotopy.mul_apply (F : Homotopy f₀ f₁) (H : Homotopy g₀ g₁) (x : I × X) :
    F.mul H x = F x * H x :=
  (rfl)

/-- Pointwise products of homotopic maps into a space with a continuous multiplication are
homotopic. -/
@[to_additive /-- Pointwise sums of homotopic maps into a space with a continuous addition are
homotopic. -/]
theorem Homotopic.mul (hf : f₀.Homotopic f₁) (hg : g₀.Homotopic g₁) :
    (f₀ * g₀).Homotopic (f₁ * g₁) :=
  hf.map2 Homotopy.mul hg

end Mul

section Inv

variable [Inv G] [ContinuousInv G] {f₀ f₁ : C(X, G)}

/-- The pointwise inverse `(t, x) ↦ (F (t, x))⁻¹` of a homotopy `F : f₀ ≃ f₁` of maps into a
space with a continuous inversion, a homotopy `f₀⁻¹ ≃ f₁⁻¹`. -/
@[to_additive /-- The pointwise negation `(t, x) ↦ -F (t, x)` of a homotopy `F : f₀ ≃ f₁` of maps
into a space with a continuous negation, a homotopy `-f₀ ≃ -f₁`. -/]
def Homotopy.inv (F : Homotopy f₀ f₁) : Homotopy f₀⁻¹ f₁⁻¹ where
  toFun x := (F x)⁻¹
  continuous_toFun := F.continuous.inv
  map_zero_left x := by simp
  map_one_left x := by simp

@[to_additive (attr := simp)]
theorem Homotopy.inv_apply (F : Homotopy f₀ f₁) (x : I × X) : F.inv x = (F x)⁻¹ :=
  (rfl)

/-- Pointwise inverses of homotopic maps into a space with a continuous inversion are
homotopic. -/
@[to_additive /-- Pointwise negations of homotopic maps into a space with a continuous negation
are homotopic. -/]
theorem Homotopic.inv (hf : f₀.Homotopic f₁) : f₀⁻¹.Homotopic f₁⁻¹ :=
  hf.map Homotopy.inv

end Inv

section Group

variable [Group G] [IsTopologicalGroup G]

variable (X G) in
/-- The maps into a topological group homotopic to the constant map `1`, a normal subgroup of
`C(X, G)` under pointwise multiplication (`ContinuousMap.homotopicOneSubgroup.normal`). -/
def homotopicOneSubgroup : Subgroup C(X, G) where
  carrier := {f | f.Homotopic 1}
  mul_mem' {f g} hf hg := by simpa using Homotopic.mul hf hg
  one_mem' := Homotopic.refl 1
  inv_mem' {f} hf := by simpa using Homotopic.inv hf

@[simp]
theorem mem_homotopicOneSubgroup {f : C(X, G)} : f ∈ homotopicOneSubgroup X G ↔ f.Homotopic 1 :=
  Iff.rfl

instance homotopicOneSubgroup.normal : (homotopicOneSubgroup X G).Normal :=
  ⟨fun f hf g ↦ by simpa using ((Homotopic.refl g).mul hf).mul (Homotopic.refl g⁻¹)⟩

/-- **Free homotopies of maps into a topological group can be made relative to a point.** Two maps
`f g : X → G` with `f q = g q` are homotopic relative to `q` exactly when they are homotopic: a
free homotopy `H` is corrected to `(t, x) ↦ H (t, x) * (H (t, q))⁻¹ * f q`. -/
theorem homotopicRel_singleton_iff_homotopic_of_apply_eq {f g : C(X, G)} {q : X}
    (hfg : f q = g q) : f.HomotopicRel g {q} ↔ f.Homotopic g := by
  refine ⟨HomotopicRel.homotopic, fun ⟨H⟩ ↦ ⟨⟨⟨⟨fun p ↦ H p * (H (p.1, q))⁻¹ * f q, by fun_prop⟩,
    fun x ↦ ?_, fun x ↦ ?_⟩, fun t x hx ↦ ?_⟩⟩⟩
  · simp
  · simp [hfg]
  · obtain rfl := Set.mem_singleton_iff.1 hx
    simp

end Group

end ContinuousMap

namespace TauCeti

open ContinuousMap

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

variable (X G) in
/-- The group `[X, G]` of free homotopy classes of maps from `X` into a topological group `G`, with
the pointwise product: the quotient of `C(X, G)` by the normal subgroup of maps homotopic to `1`. -/
def HomotopyClassGroup : Type _ :=
  C(X, G) ⧸ homotopicOneSubgroup X G

namespace HomotopyClassGroup

instance : Group (HomotopyClassGroup X G) :=
  inferInstanceAs (Group (C(X, G) ⧸ homotopicOneSubgroup X G))

instance : Inhabited (HomotopyClassGroup X G) := ⟨1⟩

variable (X G) in
/-- The quotient homomorphism sending a map `X → G` to its homotopy class. -/
def mk : C(X, G) →* HomotopyClassGroup X G :=
  QuotientGroup.mk' _

/-- Every homotopy class is the class of a map. -/
theorem mk_surjective : Function.Surjective (mk X G) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the quotient map consists of the maps homotopic to `1`. -/
@[simp]
theorem ker_mk : (mk X G).ker = homotopicOneSubgroup X G :=
  QuotientGroup.ker_mk' _

/-- A map represents the identity class exactly when it is homotopic to the constant map `1`. -/
theorem mk_eq_one_iff {f : C(X, G)} : mk X G f = 1 ↔ f.Homotopic 1 := by
  rw [← MonoidHom.mem_ker, ker_mk, mem_homotopicOneSubgroup]

/-- **Two maps into a topological group have the same class exactly when they are homotopic.** -/
theorem mk_eq_mk_iff {f g : C(X, G)} : mk X G f = mk X G g ↔ f.Homotopic g := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff, div_eq_mul_inv]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using h.mul (Homotopic.refl g)
  · simpa using h.mul (Homotopic.refl g⁻¹)

section Lift

variable {H : Type*} [Group H]

/-- A homomorphism out of `C(X, G)` that is trivial on every map homotopic to `1` descends to
`[X, G]`. -/
def lift (φ : C(X, G) →* H) (hφ : ∀ f : C(X, G), f.Homotopic 1 → φ f = 1) :
    HomotopyClassGroup X G →* H :=
  QuotientGroup.lift _ φ hφ

/-- The descended homomorphism sends the class of `f` to `φ f`. -/
@[simp]
theorem lift_mk (φ : C(X, G) →* H) (hφ : ∀ f : C(X, G), f.Homotopic 1 → φ f = 1) (f : C(X, G)) :
    lift φ hφ (mk X G f) = φ f :=
  (rfl)

/-- Two homomorphisms out of `[X, G]` agreeing on every class `mk X G f` are equal. -/
@[ext]
theorem hom_ext {ψ ψ' : HomotopyClassGroup X G →* H} (h : ψ.comp (mk X G) = ψ'.comp (mk X G)) :
    ψ = ψ' :=
  QuotientGroup.monoidHom_ext _ h

end Lift

section Eval

variable (G) in
/-- **Evaluation at a point**: the homomorphism `[X, G] →* π₀(G)` sending the class of `f` to the
path component of `f q`. It is well defined because a homotopy moves `f q` along a path. -/
def eval (q : X) : HomotopyClassGroup X G →* G ⧸ Subgroup.pathComponentOne G :=
  lift ((QuotientGroup.mk' _).comp ((Pi.evalMonoidHom (fun _ ↦ G) q).comp coeFnMonoidHom))
    fun _ ⟨F⟩ ↦ QuotientGroup.mk_eq_one_iff_joined_pathComponentOne.2 ⟨F.evalAt q⟩

@[simp]
theorem eval_mk (q : X) (f : C(X, G)) : eval G q (mk X G f) = (f q : G ⧸ _) :=
  (rfl)

variable (X) in
/-- **Classes of constant maps**: the homomorphism `π₀(G) →* [X, G]` sending the path component of
`g` to the class of the constant map at `g`. It is well defined because a path from `g` to `g'` is
a homotopy between the constant maps. -/
def const : G ⧸ Subgroup.pathComponentOne G →* HomotopyClassGroup X G :=
  QuotientGroup.lift _
    ((mk X G).comp { toFun := ContinuousMap.const X, map_one' := rfl, map_mul' := fun _ _ ↦ rfl })
    fun g hg ↦ by
      obtain ⟨p⟩ := QuotientGroup.mk_eq_one_iff_joined_pathComponentOne.1
        ((QuotientGroup.eq_one_iff g).2 hg)
      exact mk_eq_one_iff.2 ⟨p.toHomotopyConst⟩

@[simp]
theorem const_mk (g : G) : const X (g : G ⧸ Subgroup.pathComponentOne G) =
    mk X G (ContinuousMap.const X g) :=
  (rfl)

/-- **Evaluation is split by constant maps**: the constant map at `g` takes the value `g` at `q`. -/
@[simp]
theorem eval_const (q : X) (a : G ⧸ Subgroup.pathComponentOne G) : eval G q (const X a) = a := by
  induction a using QuotientGroup.induction_on with
  | H g => rfl

/-- Evaluation at a point is surjective. -/
theorem eval_surjective (q : X) : Function.Surjective (eval G q) :=
  fun a ↦ ⟨const X a, eval_const q a⟩

/-- **The kernel of evaluation at `q`** consists of the classes of maps sending `q` to `1`: a map
`f` with `f q` in the identity component is homotopic to `x ↦ f x * (f q)⁻¹`. -/
theorem mem_ker_eval_iff {q : X} {a : HomotopyClassGroup X G} :
    a ∈ (eval G q).ker ↔ ∃ f : C(X, G), f q = 1 ∧ mk X G f = a := by
  refine ⟨fun ha ↦ ?_, fun ⟨f, hf, hfa⟩ ↦ by simp [← hfa, hf]⟩
  obtain ⟨f, rfl⟩ := mk_surjective a
  rw [MonoidHom.mem_ker, eval_mk] at ha
  refine ⟨f * ContinuousMap.const X (f q)⁻¹, by simp, ?_⟩
  rw [map_mul, ← const_mk, QuotientGroup.mk_inv, ha, inv_one, map_one, mul_one]

/-- **Based maps have the same class exactly when they are homotopic relative to the base
point.** -/
theorem mk_eq_mk_iff_homotopicRel {q : X} {f g : C(X, G)} (hfg : f q = g q) :
    mk X G f = mk X G g ↔ f.HomotopicRel g {q} := by
  rw [mk_eq_mk_iff, homotopicRel_singleton_iff_homotopic_of_apply_eq hfg]

end Eval

section Discrete

variable [DiscreteTopology X]

variable (X G) in
/-- **Homotopy classes of maps out of a discrete space**: for discrete `X`, the class of a map
`f : X → G` is determined by the path components of its values, and every family of path
components occurs, so `[X, G] ≃* (X → π₀(G))`. -/
noncomputable def piMulEquivOfDiscrete :
    HomotopyClassGroup X G ≃* (X → G ⧸ Subgroup.pathComponentOne G) :=
  MulEquiv.ofBijective (MonoidHom.pi fun q ↦ eval G q) <| by
    refine ⟨(injective_iff_map_eq_one _).2 fun a ha ↦ ?_, fun φ ↦ ?_⟩
    · -- Each value is joined to `1`, and on a discrete space these paths form a homotopy.
      obtain ⟨f, rfl⟩ := mk_surjective a
      have hf (q : X) : Joined (f q) 1 :=
        QuotientGroup.mk_eq_one_iff_joined_pathComponentOne.1 (congrFun ha q)
      refine mk_eq_one_iff.2 ⟨⟨⟨fun p ↦ (hf p.2).somePath p.1,
        continuous_prod_of_discrete_right.2 fun q ↦ (hf q).somePath.continuous⟩,
        fun q ↦ by simp, fun q ↦ by simp⟩⟩
    · -- On a discrete space every choice of representatives is continuous.
      refine ⟨mk X G ⟨fun q ↦ (φ q).out, continuous_of_discreteTopology⟩, funext fun q ↦ ?_⟩
      simp

@[simp]
theorem piMulEquivOfDiscrete_mk (f : C(X, G)) (q : X) :
    piMulEquivOfDiscrete X G (mk X G f) q = (f q : G ⧸ Subgroup.pathComponentOne G) :=
  (rfl)

end Discrete

end HomotopyClassGroup

end TauCeti
