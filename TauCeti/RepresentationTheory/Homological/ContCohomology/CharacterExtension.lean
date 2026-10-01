/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# The extension of `𝔽_p` by `𝔽_p` attached to a character

Let `G` be a topological group and `χ : G → 𝔽_p` a continuous character. The **extension module**
`E(χ)` is `𝔽_p²` with `g` acting by the unipotent matrix `[[1, χ g], [0, 1]]`,

```text
g • (a, b) = (a + χ(g) b, b).
```

It sits in the short exact sequence of discrete `G`-modules

```text
0 → 𝔽_p → E(χ) → 𝔽_p → 0,
```

which is the extension of the trivial module `𝔽_p` by itself classified by `χ`: its connecting map
`δ : H¹(G, 𝔽_p) → H²(G, 𝔽_p)` is the cup product with `χ`
(`TauCeti.CharacterExtension.explicitDelta1_shortExact`). This is the module through which a
character that cups trivially with all of `H¹(G, 𝔽_p)` becomes visible in degree two: the
connecting map then vanishes, and `H²(G, E(χ))` is as large as the two outer terms allow.

If `χ` is onto, with kernel `N`, then `E(χ)` is a quotient of the permutation module
`Coind_N^G 𝔽_p = 𝔽_p[G/N]`: the trace of the coinduced map of the inclusion `𝔽_p → E(χ)` of the
second coordinate is a `G`-equivariant surjection
(`TauCeti.CharacterExtension.coindTrace_surjective`). Through Shapiro's lemma, this compares the
`H²` of `E(χ)` with the `H²` of the subgroup `N`.

The trivial modules of the short exact sequence are placed in the universe of `G` by `ULift`, as
the comparison of the explicit and canonical long exact sequences requires.

## Main definitions

* `TauCeti.CharacterExtension`: the extension module `E(χ)`, a discrete `G`-module with continuous
  action, finite when `p ≠ 0`.
* `TauCeti.CharacterExtension.shortExact`: the short exact sequence `0 → 𝔽_p → E(χ) → 𝔽_p → 0`.
* `TauCeti.CharacterExtension.coindTrace`: the equivariant map `Coind_N^G 𝔽_p → E(χ)` for a
  subgroup `N` on which `χ` vanishes.

## Main results

* `TauCeti.CharacterExtension.explicitDelta1_shortExact`: the connecting map of the short exact
  sequence is the cup product with `χ`.
* `TauCeti.CharacterExtension.coindTrace_surjective`: for `χ` onto and `N = ker χ`, the map
  `Coind_N^G 𝔽_p → E(χ)` is onto.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-- **The extension module `E(χ)` of a character** `χ : G → 𝔽_p`, written multiplicatively as a
continuous homomorphism to `Multiplicative (ZMod p)`: the additive group `𝔽_p²`, on which `g` acts
by `g • (a, b) = (a + χ(g) b, b)`. The character is a parameter of the type so that the action can
be an instance, and the module is placed in the universe of `G`. -/
@[ext]
structure CharacterExtension (χ : G →ₜ* Multiplicative (ZMod p)) : Type u where
  /-- The coordinate on the invariant line `𝔽_p ⊆ E(χ)`. -/
  fst : ZMod p
  /-- The coordinate on the quotient `E(χ) → 𝔽_p`. -/
  snd : ZMod p

namespace CharacterExtension

variable (χ : G →ₜ* Multiplicative (ZMod p))

instance : AddCommGroup (CharacterExtension χ) :=
  Equiv.addCommGroup ⟨fun x ↦ (x.fst, x.snd), fun x ↦ ⟨x.1, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

@[simp] theorem fst_zero : (0 : CharacterExtension χ).fst = 0 := (rfl)

@[simp] theorem snd_zero : (0 : CharacterExtension χ).snd = 0 := (rfl)

@[simp] theorem fst_add (x y : CharacterExtension χ) : (x + y).fst = x.fst + y.fst := (rfl)

@[simp] theorem snd_add (x y : CharacterExtension χ) : (x + y).snd = x.snd + y.snd := (rfl)

@[simp] theorem fst_neg (x : CharacterExtension χ) : (-x).fst = -x.fst := (rfl)

@[simp] theorem snd_neg (x : CharacterExtension χ) : (-x).snd = -x.snd := (rfl)

@[simp] theorem fst_sub (x y : CharacterExtension χ) : (x - y).fst = x.fst - y.fst := (rfl)

@[simp] theorem snd_sub (x y : CharacterExtension χ) : (x - y).snd = x.snd - y.snd := (rfl)

instance : TopologicalSpace (CharacterExtension χ) := ⊥

instance : DiscreteTopology (CharacterExtension χ) := ⟨rfl⟩

instance [NeZero p] : Finite (CharacterExtension χ) :=
  Finite.of_injective (fun x : CharacterExtension χ ↦ (x.fst, x.snd)) fun _ _ h ↦
    CharacterExtension.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- `g` acts on `E(χ)` by the unipotent matrix `[[1, χ g], [0, 1]]`. -/
instance : SMul G (CharacterExtension χ) where
  smul g x := ⟨x.fst + Multiplicative.toAdd (χ g) * x.snd, x.snd⟩

@[simp]
theorem fst_smul (g : G) (x : CharacterExtension χ) :
    (g • x).fst = x.fst + Multiplicative.toAdd (χ g) * x.snd :=
  (rfl)

@[simp]
theorem snd_smul (g : G) (x : CharacterExtension χ) : (g • x).snd = x.snd := (rfl)

/-- The action of `G` on `E(χ)` is distributive, because `χ` is a homomorphism. -/
instance : DistribMulAction G (CharacterExtension χ) where
  one_smul x := CharacterExtension.ext (by simp) rfl
  mul_smul g h x := CharacterExtension.ext (by simp [toAdd_mul]; ring) rfl
  smul_zero g := CharacterExtension.ext (by simp) rfl
  smul_add g x y := CharacterExtension.ext (by simp; ring) rfl

/-- The action of `G` on the discrete module `E(χ)` is continuous, because `χ` is. -/
instance : ContinuousSMul G (CharacterExtension χ) where
  continuous_smul :=
    (continuous_of_discreteTopology (f := fun q : ZMod p × CharacterExtension χ ↦
      (⟨q.2.fst + q.1 * q.2.snd, q.2.snd⟩ : CharacterExtension χ))).comp
      (((continuous_toAdd.comp χ.continuous).comp continuous_fst).prodMk continuous_snd)

/-- An element of the kernel of `χ` acts trivially on `E(χ)`. -/
theorem smul_eq_self_of_apply_eq_one {g : G} (hg : χ g = 1) (x : CharacterExtension χ) :
    g • x = x :=
  CharacterExtension.ext (by simp [hg]) rfl

/-! ### The short exact sequence `0 → 𝔽_p → E(χ) → 𝔽_p → 0` -/

section ShortExact

variable [DistribMulAction G (ZMod p)] (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include htriv

/-- **The short exact sequence `0 → 𝔽_p → E(χ) → 𝔽_p → 0`** of discrete `G`-modules, for a
trivial action on `𝔽_p`: the inclusion of the first coordinate and the projection to the second.
The trivial modules are lifted to the universe of `G`. -/
def shortExact :
    DiscreteShortExact G (ULift.{u} (ZMod p)) (CharacterExtension χ) (ULift.{u} (ZMod p)) where
  incl :=
    { toFun a := ⟨a.down, 0⟩
      map_zero' := rfl
      map_add' a b := CharacterExtension.ext rfl (add_zero 0).symm }
  proj :=
    { toFun x := ULift.up x.snd
      map_zero' := rfl
      map_add' _ _ := rfl }
  incl_equivariant g a := CharacterExtension.ext (by simp [htriv]) rfl
  proj_equivariant g x := ULift.ext (by simp [htriv])
  incl_injective a b h := ULift.ext (congrArg fst h)
  proj_surjective a := ⟨⟨0, a.down⟩, rfl⟩
  exact x := ⟨fun h ↦ ⟨ULift.up x.fst, CharacterExtension.ext rfl (congrArg ULift.down h).symm⟩,
    by rintro ⟨a, rfl⟩; rfl⟩

@[simp]
theorem shortExact_incl_apply (a : ULift.{u} (ZMod p)) :
    (shortExact χ htriv).incl a = ⟨a.down, 0⟩ :=
  (rfl)

@[simp]
theorem shortExact_proj_apply (x : CharacterExtension χ) :
    (shortExact χ htriv).proj x = ULift.up x.snd :=
  (rfl)

variable [IsTopologicalGroup G] [ContinuousSMul G (ZMod p)]
  [ContinuousSMul G (ULift.{u} (ZMod p))]

/-- **The connecting map of `0 → 𝔽_p → E(χ) → 𝔽_p → 0` is the cup product with `χ`**: for a class
`x ∈ H¹(G, 𝔽_p)`, `δ x = χ ⌣ x` in `H²(G, 𝔽_p)`, the cup product being taken for the scalar
multiplication `𝔽_p × 𝔽_p → 𝔽_p` and `χ` being read as a class through the identification of
`H¹(G, 𝔽_p)` with the continuous characters. -/
theorem explicitDelta1_shortExact (x : H1 G (ULift.{u} (ZMod p))) :
    (shortExact χ htriv).explicitDelta1 x =
      explicitCup11 G (ZMod p) (ULift.{u} (ZMod p)) (ULift.{u} (ZMod p))
        (smulAddHom (ZMod p) (ULift.{u} (ZMod p))) continuous_of_discreteTopology
        (fun g a b ↦ by ext; simp [htriv])
        ((H1EquivOfSmulEqSelf htriv).symm (Additive.ofMul χ)) x := by
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    obtain ⟨hfc, hf1⟩ := mem_Z1_iff.1 f.2
    -- the lift `g ↦ (0, ψ g)` of the cocycle `ψ`, whose coboundary is `(g, h) ↦ (χ g ψ h, 0)`
    have hec : Continuous fun g : G ↦ (⟨0, ((f : G → ULift (ZMod p)) g).down⟩ :
        CharacterExtension χ) :=
      (continuous_of_discreteTopology (f := fun a : ULift.{u} (ZMod p) ↦
        (⟨0, a.down⟩ : CharacterExtension χ))).comp hfc
    have hmul : ∀ g h : G, (f : G → ULift (ZMod p)) (g * h) =
        (f : G → ULift (ZMod p)) g + (f : G → ULift (ZMod p)) h := fun g h ↦ by
      have h1 := hf1 g h
      have hg : g • (f : G → ULift (ZMod p)) h = (f : G → ULift (ZMod p)) h :=
        ULift.ext (by simp [htriv])
      rw [hg] at h1
      rw [h1, add_comm]
    have hae : ∀ g h : G, (shortExact χ htriv).incl
        (ULift.up (Multiplicative.toAdd (χ g) * ((f : G → ULift (ZMod p)) h).down)) =
        g • (⟨0, ((f : G → ULift (ZMod p)) h).down⟩ : CharacterExtension χ) -
          ⟨0, ((f : G → ULift (ZMod p)) (g * h)).down⟩ +
          ⟨0, ((f : G → ULift (ZMod p)) g).down⟩ := fun g h ↦ by
      refine CharacterExtension.ext (by simp) ?_
      simp only [shortExact_incl_apply, snd_add, snd_sub, snd_smul, hmul g h, ULift.add_down]
      ring
    have ha := (shortExact χ htriv).mem_Z2_of_incl_comp_eq_d1 hec
      (a := fun q : G × G ↦
        ULift.up (Multiplicative.toAdd (χ q.1) * ((f : G → ULift (ZMod p)) q.2).down))
      hae
    have hδ := (shortExact χ htriv).explicitDelta1_apply f hec (fun g ↦ rfl) ha hae
    simp only [QuotientAddGroup.mk'_apply] at hδ
    rw [hδ, H1EquivOfSmulEqSelf_symm_apply, explicitCup11_mk]
    refine congrArg (H2pi G (ULift (ZMod p))) (Subtype.ext (funext fun q ↦ ULift.ext ?_))
    obtain ⟨g, h⟩ := q
    have hg : g • (f : G → ULift (ZMod p)) h = (f : G → ULift (ZMod p)) h :=
      ULift.ext (by simp [htriv])
    simp [hg, smulAddHom_apply]

end ShortExact

/-! ### The surjection from the permutation module -/

section Coind

variable [ContinuousMul G] {N : Subgroup G} [N.FiniteIndex] [DistribMulAction G (ZMod p)]
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m) (hN : ∀ n ∈ N, χ n = 1)

/-- The inclusion `b ↦ (0, b)` of the second coordinate of `E(χ)`, as an `N`-equivariant map
`𝔽_p → E(χ)` for a subgroup `N` on which `χ` vanishes. -/
private def inclSnd : ZMod p →ₗ[ℤ] CharacterExtension χ :=
  AddMonoidHom.toIntLinearMap
    { toFun b := ⟨0, b⟩
      map_zero' := rfl
      map_add' _ _ := CharacterExtension.ext (add_zero 0).symm rfl }

omit [ContinuousMul G] [N.FiniteIndex] in
include htriv hN in
private theorem inclSnd_smul (n : N) (b : ZMod p) :
    inclSnd χ (n • b) = n • inclSnd χ b := by
  rw [Subgroup.smul_def, htriv, Subgroup.smul_def,
    smul_eq_self_of_apply_eq_one χ (hN n n.2)]

/-- **The trace map `Coind_N^G 𝔽_p → E(χ)`** for a subgroup `N` of finite index on which `χ`
vanishes: coinduce the `N`-equivariant inclusion `b ↦ (0, b)` of the second coordinate, and take
the trace. It is `G`-equivariant, and onto when `N = ker χ` and `χ` is onto
(`TauCeti.CharacterExtension.coindTrace_surjective`). -/
noncomputable def coindTrace : DiscreteCoind G N (ZMod p) →+[G] CharacterExtension χ where
  toFun f := DiscreteCoind.trace G N (CharacterExtension χ)
    (DiscreteCoind.map (inclSnd χ) (inclSnd_smul χ htriv hN) f)
  map_smul' g f := by
    rw [DiscreteCoind.map_smul, map_smul, MonoidHom.id_apply]
  map_zero' := by rw [map_zero, map_zero]
  map_add' f f' := by rw [map_add, map_add]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The trace map sums the second-coordinate inclusions of the values of `f` over a choice of coset
representatives. -/
theorem coindTrace_apply (f : DiscreteCoind G N (ZMod p)) :
    coindTrace χ htriv hN f = ∑ x : G ⧸ N, x.out • (⟨0, f x.out⁻¹⟩ : CharacterExtension χ) :=
  (DiscreteCoind.trace_apply _).trans (Finset.sum_congr rfl fun x _ ↦ by
    rw [DiscreteCoind.map_apply]
    rfl)

omit [ContinuousMul G] [N.FiniteIndex] [DistribMulAction G (ZMod p)] in
/-- The function `g ↦ b` if `χ g = 1` and `g ↦ 0` otherwise is locally constant. -/
private theorem isLocallyConstant_ite (b : ZMod p) :
    IsLocallyConstant fun g : G ↦ if χ g = 1 then b else 0 :=
  (IsLocallyConstant.of_discrete fun m : Multiplicative (ZMod p) ↦
    if m = 1 then b else 0).comp_continuous χ.continuous

omit [ContinuousMul G] [N.FiniteIndex] in
include htriv hN in
/-- The element of `Coind_N^G 𝔽_p` that is `b` on `ker χ` and `0` off it. -/
private noncomputable def kerIndicator (b : ZMod p) : DiscreteCoind G N (ZMod p) :=
  DiscreteCoind.mk G N (ZMod p) (fun g ↦ if χ g = 1 then b else 0) (isLocallyConstant_ite χ b)
    fun n g ↦ by simp only [map_mul, hN n n.2, one_mul, Subgroup.smul_def, htriv]

omit [ContinuousMul G] [N.FiniteIndex] in
private theorem kerIndicator_apply (b : ZMod p) (g : G) :
    kerIndicator χ htriv hN b g = if χ g = 1 then b else 0 :=
  DiscreteCoind.mk_apply _ _ _ _

/-- The trace map sends the indicator of `ker χ` with value `b` to `(0, b)`, when `N = ker χ`. -/
private theorem coindTrace_kerIndicator (hNker : ∀ g : G, χ g = 1 → g ∈ N) (b : ZMod p) :
    coindTrace χ htriv hN (kerIndicator χ htriv hN b) = ⟨0, b⟩ := by
  -- only the coset of `1` contributes to the trace
  have hout : ∀ x : G ⧸ N, x.out ∈ N ↔ x = ((1 : G) : G ⧸ N) := fun x ↦ by
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq, inv_one, one_mul]
  rw [coindTrace_apply, Finset.sum_eq_single ((1 : G) : G ⧸ N)]
  · have h1 : χ ((1 : G) : G ⧸ N).out = 1 := hN _ ((hout _).2 rfl)
    have h1' : χ ((1 : G) : G ⧸ N).out⁻¹ = 1 := by rw [map_inv, h1, inv_one]
    rw [kerIndicator_apply, ite_eq_left h1']
    exact smul_eq_self_of_apply_eq_one χ h1 _
  · intro x _ hx
    have hx' : χ x.out⁻¹ ≠ 1 := fun h ↦ hx <| (hout x).1 <| by
      rw [map_inv, inv_eq_one] at h
      exact hNker _ h
    rw [kerIndicator_apply, ite_eq_right hx']
    exact (congrArg (x.out • ·) (CharacterExtension.ext rfl rfl : (⟨0, 0⟩ : CharacterExtension χ) =
      0)).trans (smul_zero _)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The trace map `Coind_N^G 𝔽_p → E(χ)` is onto** when `χ` is onto and `N` is its kernel. -/
theorem coindTrace_surjective (hNker : ∀ g : G, χ g = 1 → g ∈ N)
    (hχ : Function.Surjective χ) : Function.Surjective (coindTrace χ htriv hN) := by
  intro x
  obtain ⟨s, hs⟩ := hχ (Multiplicative.ofAdd 1)
  refine ⟨s • kerIndicator χ htriv hN x.fst - kerIndicator χ htriv hN x.fst +
    kerIndicator χ htriv hN x.snd, ?_⟩
  rw [map_add, map_sub, map_smul, coindTrace_kerIndicator χ htriv hN hNker,
    coindTrace_kerIndicator χ htriv hN hNker]
  refine CharacterExtension.ext ?_ ?_ <;> simp [hs]

end Coind

end CharacterExtension

end TauCeti
