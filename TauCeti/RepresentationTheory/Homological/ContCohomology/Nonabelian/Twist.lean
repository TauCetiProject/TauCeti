/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# Twisting continuous nonabelian first cohomology by a cocycle

Let a group `G` with a topology act on a topological group `A` by group automorphisms, and let
`c` be a continuous `1`-cocycle of `G` with values in `A`. The **twist** `₍c₎A` of `A` by `c` is
the topological group `A` on which `g : G` acts by the inner twist

`g ⋆ x = c g * g • x * (c g)⁻¹`.

This is again an action by group automorphisms, and continuous when the original action is. For
`A` the automorphism group of an object `X`, `₍c₎A` is the automorphism group of the form of `X`
classified by `c` (Serre, I.5.3).

Right multiplication by `c` turns cocycles of the twist into cocycles of `A`: the map
`d ↦ (g ↦ d g * c g)` is a bijection `Z¹(G, ₍c₎A) ≃ Z¹(G, A)`, with inverse
`f ↦ (g ↦ f g * (c g)⁻¹)`.
It intertwines the gauge actions of `A` on both sides, so it descends to a bijection

`H¹(G, ₍c₎A) ≃ H¹(G, A)`

which sends the base point to the class of `c`. It is a bijection of underlying sets only: the
target is pointed at `[c]` rather than at its own base point. Through it, the fibre of a map of
`H¹` over the class of a cocycle becomes, after twisting, a fibre over the base point; the
compatibility with equivariant coefficient maps needed for this is
`TauCeti.NonabelianH1.map_twistEquiv`.

The elements of `₍c₎A` form the one-field structure `TauCeti.NonabelianH1.Twist c`, so that the
twisted action cannot be confused with the original one; `Twist.ofOriginal` and
`Twist.toOriginal` pass between `A` and `₍c₎A`, and `Twist.continuousMulEquiv c` bundles them as
an isomorphism of topological groups, which is not `G`-equivariant.

## Main definitions

* `TauCeti.NonabelianH1.Twist c`: the twist `₍c₎A` of `A` by the cocycle `c`, a topological group
  with the twisted action `g ⋆ x = c g * g • x * (c g)⁻¹`.
* `TauCeti.NonabelianH1.Twist.continuousMulEquiv c`: the underlying identification `₍c₎A ≃ₜ* A`.
* `TauCeti.NonabelianH1.Twist.map`: the map `₍c₎A →ₜ* ₍φ ∘ c₎A'` induced by an equivariant
  continuous homomorphism `φ : A →ₜ* A'`.
* `TauCeti.NonabelianH1.Cocycle.twistEquiv c`: the bijection `Z¹(G, ₍c₎A) ≃ Z¹(G, A)`,
  `d ↦ (g ↦ d g * c g)`.
* `TauCeti.NonabelianH1.twistEquiv c`: the induced bijection `H¹(G, ₍c₎A) ≃ H¹(G, A)`.

## Main results

* `TauCeti.NonabelianH1.Twist.toOriginal_smul`: the twisted action is `c g * g • x * (c g)⁻¹`.
* `TauCeti.NonabelianH1.Twist.mem_fixedPoints_iff`: the invariants of `₍c₎A` are the elements
  `x` with `c g * g • x = x * c g` for all `g`.
* `TauCeti.NonabelianH1.Cocycle.twistEquiv_twist`: twisting intertwines the gauge actions.
* `TauCeti.NonabelianH1.twistEquiv_one`: the base point of `H¹(G, ₍c₎A)` goes to `[c]`.
* `TauCeti.NonabelianH1.map_twistEquiv`: twisting commutes with the maps induced by equivariant
  continuous homomorphisms.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.3, Proposition 35bis.
* M. Kim, *The motivic fundamental group of `P¹ ∖ {0, 1, ∞}` and the theorem of Siegel*,
  Invent. Math. 161 (2005), §1, proof of Proposition 1.
-/

public section

namespace TauCeti

namespace NonabelianH1

variable {G A : Type*} [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]
  [MulDistribMulAction G A]

/-- The **twist** `₍c₎A` of the `G`-group `A` by a cocycle `c`: a copy of the topological group
`A`, on which `g : G` acts by `x ↦ c g * g • x * (c g)⁻¹`
(`TauCeti.NonabelianH1.Twist.toOriginal_smul`). -/
@[ext]
structure Twist (c : Cocycle G A) where
  /-- The element of the twist `₍c₎A` with a given underlying element of `A`. -/
  ofOriginal ::
  /-- The underlying element of `A` of an element of the twist `₍c₎A`. -/
  toOriginal : A

namespace Twist

variable {c : Cocycle G A}

@[simp]
theorem toOriginal_ofOriginal (a : A) : (ofOriginal a : Twist c).toOriginal = a :=
  (rfl)

@[simp]
theorem ofOriginal_toOriginal (x : Twist c) : ofOriginal x.toOriginal = x :=
  (rfl)

instance : Group (Twist c) :=
  Equiv.group ⟨toOriginal, ofOriginal, fun _ ↦ rfl, fun _ ↦ rfl⟩

@[simp]
theorem toOriginal_one : (1 : Twist c).toOriginal = 1 :=
  (rfl)

@[simp]
theorem toOriginal_mul (x y : Twist c) : (x * y).toOriginal = x.toOriginal * y.toOriginal :=
  (rfl)

@[simp]
theorem toOriginal_inv (x : Twist c) : x⁻¹.toOriginal = x.toOriginal⁻¹ :=
  (rfl)

@[simp]
theorem ofOriginal_one : (ofOriginal 1 : Twist c) = 1 :=
  (rfl)

@[simp]
theorem ofOriginal_mul (a b : A) : (ofOriginal (a * b) : Twist c) = ofOriginal a * ofOriginal b :=
  (rfl)

@[simp]
theorem ofOriginal_inv (a : A) : (ofOriginal a⁻¹ : Twist c) = (ofOriginal a)⁻¹ :=
  (rfl)

/-- The twist carries the topology of `A`. -/
instance : TopologicalSpace (Twist c) :=
  .induced toOriginal ‹_›

@[continuity, fun_prop]
theorem continuous_toOriginal : Continuous (toOriginal : Twist c → A) :=
  continuous_induced_dom

@[continuity, fun_prop]
theorem continuous_ofOriginal : Continuous (ofOriginal : A → Twist c) :=
  continuous_induced_rng.2 continuous_id

variable (c) in
/-- The underlying identification `₍c₎A ≃ₜ* A` of topological groups. It need not be
`G`-equivariant: it carries the twisted action to `x ↦ c g * g • x * (c g)⁻¹`. -/
def continuousMulEquiv : Twist c ≃ₜ* A where
  toFun := toOriginal
  invFun := ofOriginal
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_toOriginal
  continuous_invFun := continuous_ofOriginal

@[simp]
theorem coe_continuousMulEquiv : ⇑(continuousMulEquiv c) = toOriginal :=
  (rfl)

@[simp]
theorem coe_continuousMulEquiv_symm : ⇑(continuousMulEquiv c).symm = ofOriginal :=
  (rfl)

instance [IsTopologicalGroup A] : IsTopologicalGroup (Twist c) :=
  Topology.IsInducing.isTopologicalGroup (continuousMulEquiv c) ⟨rfl⟩

/-- The twisted action `g ⋆ x = c g * g • x * (c g)⁻¹` of `G` on `₍c₎A`. -/
instance : SMul G (Twist c) :=
  ⟨fun g x ↦ ofOriginal (c g * g • x.toOriginal * (c g)⁻¹)⟩

/-- The **twisted action**: `g ⋆ x = c g * g • x * (c g)⁻¹`. -/
@[simp]
theorem toOriginal_smul (g : G) (x : Twist c) :
    (g • x).toOriginal = c g * g • x.toOriginal * (c g)⁻¹ :=
  (rfl)

/-- The twisted action is an action by group automorphisms. -/
instance : MulDistribMulAction G (Twist c) where
  smul := (· • ·)
  one_smul x := by ext; simp
  mul_smul g h x := by ext; simp [c.apply_mul, mul_smul, smul_mul', mul_assoc]
  smul_mul g x y := by ext; simp [smul_mul', mul_assoc]
  smul_one g := by ext; simp

/-- The twisted action is continuous when the original action is. -/
instance [IsTopologicalGroup A] [ContinuousSMul G A] : ContinuousSMul G (Twist c) where
  continuous_smul := continuous_induced_rng.2 <| by
    simp only [Function.comp_def, toOriginal_smul]
    fun_prop

/-- Where `c g` commutes with `g • x`, the twisted action of `g` on `x` is the original one. In
particular this holds for the trivial cocycle and for commutative `A`. -/
theorem toOriginal_smul_of_commute {g : G} {x : Twist c} (h : Commute (c g) (g • x.toOriginal)) :
    (g • x).toOriginal = g • x.toOriginal := by
  rw [toOriginal_smul, h.eq, mul_inv_cancel_right]

/-- `x` is fixed by `g` for the twisted action exactly when `c g * g • x = x * c g`. -/
theorem smul_eq_self_iff {g : G} {x : Twist c} :
    g • x = x ↔ c g * g • x.toOriginal = x.toOriginal * c g := by
  rw [Twist.ext_iff, toOriginal_smul, mul_inv_eq_iff_eq_mul]

/-- The **invariants of the twist**: `x` is fixed by the twisted action exactly when
`c g * g • x = x * c g` for all `g`. -/
theorem mem_fixedPoints_iff {x : Twist c} :
    x ∈ MulAction.fixedPoints G (Twist c) ↔ ∀ g, c g * g • x.toOriginal = x.toOriginal * c g := by
  simp only [MulAction.mem_fixedPoints, smul_eq_self_iff]

section Map

variable {A' : Type*} [Group A'] [TopologicalSpace A'] [MulDistribMulAction G A']

variable (c) in
/-- The map `₍c₎A →ₜ* ₍φ ∘ c₎A'` of twists induced by a `G`-equivariant continuous homomorphism
`φ : A →ₜ* A'`. It is equivariant for the twisted actions
(`TauCeti.NonabelianH1.Twist.map_smul`). -/
def map (φ : A →ₜ* A') (h : ∀ (g : G) (a : A), φ (ContinuousMonoidHom.id G g • a) = g • φ a) :
    Twist c →ₜ* Twist (c.map (ContinuousMonoidHom.id G) φ h) where
  toFun x := ofOriginal (φ x.toOriginal)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  continuous_toFun := by fun_prop

@[simp]
theorem toOriginal_map (φ : A →ₜ* A')
    (h : ∀ (g : G) (a : A), φ (ContinuousMonoidHom.id G g • a) = g • φ a) (x : Twist c) :
    (map c φ h x).toOriginal = φ x.toOriginal :=
  (rfl)

/-- The map of twists is equivariant for the twisted actions. -/
theorem map_smul (φ : A →ₜ* A')
    (h : ∀ (g : G) (a : A), φ (ContinuousMonoidHom.id G g • a) = g • φ a) (g : G) (x : Twist c) :
    map c φ h (ContinuousMonoidHom.id G g • x) = g • map c φ h x := by
  have hg : ∀ a, φ (g • a) = g • φ a := h g
  ext
  simp [hg]

end Map

end Twist

namespace Cocycle

variable [IsTopologicalGroup A] (c : Cocycle G A)

/-- **Twisting by a cocycle** on cocycles: the bijection `Z¹(G, ₍c₎A) ≃ Z¹(G, A)` sending `d` to
`g ↦ d g * c g`, with inverse `f ↦ (g ↦ f g * (c g)⁻¹)`. -/
def twistEquiv : Cocycle G (Twist c) ≃ Cocycle G A where
  toFun d :=
    { toFun g := (d g).toOriginal * c g
      continuous_toFun := by fun_prop
      map_mul' g h := by simp [d.apply_mul, c.apply_mul, smul_mul', mul_assoc] }
  invFun f :=
    { toFun g := Twist.ofOriginal (f g * (c g)⁻¹)
      continuous_toFun := by fun_prop
      map_mul' g h := by ext; simp [f.apply_mul, c.apply_mul, smul_mul', mul_assoc] }
  left_inv d := by ext; simp
  right_inv f := by ext; simp

@[simp]
theorem twistEquiv_apply (d : Cocycle G (Twist c)) (g : G) :
    c.twistEquiv d g = (d g).toOriginal * c g :=
  (rfl)

@[simp]
theorem toOriginal_twistEquiv_symm_apply (f : Cocycle G A) (g : G) :
    (c.twistEquiv.symm f g).toOriginal = f g * (c g)⁻¹ :=
  (rfl)

/-- Twisting sends the trivial cocycle of `₍c₎A` to `c`. -/
@[simp]
theorem twistEquiv_one : c.twistEquiv 1 = c := by
  ext
  simp

@[simp]
theorem twistEquiv_symm_self : c.twistEquiv.symm c = 1 :=
  c.twistEquiv.symm_apply_eq.2 c.twistEquiv_one.symm

/-- Twisting by `c` preserves and reflects the cohomology relation. -/
theorem twistEquiv_equiv_twistEquiv_iff {d d' : Cocycle G (Twist c)} :
    c.twistEquiv d ≈ c.twistEquiv d' ↔ d ≈ d' := by
  simp only [equiv_iff, twistEquiv_apply]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨Twist.ofOriginal a, fun g ↦ ?_⟩
    ext
    simp only [Twist.toOriginal_mul, Twist.toOriginal_inv, Twist.toOriginal_smul, ← mul_assoc]
    rw [eq_mul_inv_iff_mul_eq, ha g]
    simp only [mul_assoc]
  · rintro ⟨b, hb⟩
    exact ⟨b.toOriginal, fun g ↦ by simp [hb g, mul_assoc]⟩

/-- Twisting intertwines the gauge actions: twisting the gauge transform of `d` by `a` is the gauge
transform by `a` of the twisted cocycle. -/
theorem twistEquiv_twist [ContinuousSMul G A] (d : Cocycle G (Twist c)) (a : Twist c) :
    c.twistEquiv (d.twist a) = (c.twistEquiv d).twist a.toOriginal := by
  ext
  simp [mul_assoc]

section Map

variable {A' : Type*} [Group A'] [TopologicalSpace A'] [IsTopologicalGroup A']
  [MulDistribMulAction G A']

/-- Twisting commutes with mapping along a `G`-equivariant continuous homomorphism `φ`. -/
theorem map_twistEquiv (φ : A →ₜ* A')
    (h : ∀ (g : G) (a : A), φ (ContinuousMonoidHom.id G g • a) = g • φ a)
    (d : Cocycle G (Twist c)) :
    (c.twistEquiv d).map (ContinuousMonoidHom.id G) φ h =
      (c.map (ContinuousMonoidHom.id G) φ h).twistEquiv
        (d.map (ContinuousMonoidHom.id G) (Twist.map c φ h) (Twist.map_smul φ h)) := by
  ext
  simp

end Map

end Cocycle

variable [IsTopologicalGroup A] (c : Cocycle G A)

/-- **Twisting by a cocycle**: the bijection `H¹(G, ₍c₎A) ≃ H¹(G, A)` induced by
`d ↦ (g ↦ d g * c g)` on cocycles. It sends the base point to the class of `c`
(`TauCeti.NonabelianH1.twistEquiv_one`), so it preserves base points only when `c` is a
coboundary. -/
def twistEquiv : NonabelianH1 G (Twist c) ≃ NonabelianH1 G A :=
  congr c.twistEquiv fun _ _ ↦ c.twistEquiv_equiv_twistEquiv_iff.symm

@[simp]
theorem twistEquiv_mk (d : Cocycle G (Twist c)) : twistEquiv c (mk d) = mk (c.twistEquiv d) :=
  congr_mk _ _ d

@[simp]
theorem twistEquiv_symm_mk (f : Cocycle G A) :
    (twistEquiv c).symm (mk f) = mk (c.twistEquiv.symm f) :=
  congr_symm_mk _ _ f

/-- Twisting by `c` sends the base point of `H¹(G, ₍c₎A)` to the class of `c`. -/
@[simp]
theorem twistEquiv_one : twistEquiv c 1 = mk c := by
  rw [one_def, twistEquiv_mk, Cocycle.twistEquiv_one]

/-- The class of `c` corresponds to the base point of `H¹(G, ₍c₎A)`. -/
theorem twistEquiv_symm_mk_self : (twistEquiv c).symm (mk c) = 1 := by
  rw [twistEquiv_symm_mk, Cocycle.twistEquiv_symm_self, mk_one]

/-- Twisting commutes with the maps of `H¹` induced by a `G`-equivariant continuous homomorphism
`φ : A →ₜ* A'`: the square formed by `H¹(G, ₍c₎A) → H¹(G, ₍φ ∘ c₎A')` and `H¹(G, A) → H¹(G, A')`
commutes. -/
theorem map_twistEquiv {A' : Type*} [Group A'] [TopologicalSpace A'] [IsTopologicalGroup A']
    [MulDistribMulAction G A'] (φ : A →ₜ* A')
    (h : ∀ (g : G) (a : A), φ (ContinuousMonoidHom.id G g • a) = g • φ a)
    (x : NonabelianH1 G (Twist c)) :
    map (ContinuousMonoidHom.id G) φ h (twistEquiv c x) =
      twistEquiv (c.map (ContinuousMonoidHom.id G) φ h)
        (map (ContinuousMonoidHom.id G) (Twist.map c φ h) (Twist.map_smul φ h) x) := by
  induction x using induction_on with | mk d =>
  simp only [twistEquiv_mk, map_mk, Cocycle.map_twistEquiv]

end NonabelianH1

end TauCeti
