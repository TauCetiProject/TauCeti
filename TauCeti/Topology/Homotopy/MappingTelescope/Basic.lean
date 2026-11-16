/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import TauCeti.Topology.Homotopy.MappingCylinder

/-!
# The mapping telescope of a sequence of continuous maps

Given a sequence of spaces `X : ℕ → Type u` and continuous bonding maps
`f : ∀ n, C(X n, X (n + 1))`, the *mapping telescope* `TauCeti.MappingTelescope f` is the homotopy
colimit obtained from the disjoint union of cylinders `Σ n, I × X n` by gluing the top face
`{1} × X n` of the `n`-th cylinder to the bottom face `{0} × X (n + 1)` of the next cylinder along
`f n`.

Every point of the disjoint union has a unique normal representative of height strictly less than
`1`: a top-face point `⟨n, 1, x⟩` is replaced by `⟨n + 1, 0, f n x⟩` and every other point is
left unchanged. Taking the quotient by the kernel of this normalization—following the presentation
of `TauCeti.MappingCylinder`—makes all point-set identifications immediate
(`TauCeti.MappingTelescope.mkCyl_eq_mkCyl_iff`) without chaining an inductive equivalence relation
across multiple cylinders.

Each space `X n` embeds as a closed subspace of the telescope as the bottom face `{0} × X n` of
its cylinder (`TauCeti.MappingTelescope.isClosedEmbedding_incl`), each segment embeds as a closed
copy of `TauCeti.MappingCylinder (f n)`
(`TauCeti.MappingTelescope.isClosedEmbedding_fromMappingCylinder`), and the `n`-th cylinder
supplies the canonical homotopy from `incl f n` to `(incl f (n + 1)).comp (f n)`
(`TauCeti.MappingTelescope.inclHomotopy`). Separation (`T1Space` and `T2Space`) and compact
generation (`UCompactlyGeneratedSpace` and `CompactlyGeneratedSpace`) pass from the stages `X n`
directly to `TauCeti.MappingTelescope f` with no auxiliary coreflection.

## Main declarations

* `TauCeti.MappingTelescope`: the mapping telescope of `f : ∀ n, C(X n, X (n + 1))`, with cylinder
  maps `TauCeti.MappingTelescope.mkCyl`, stage inclusions `TauCeti.MappingTelescope.incl`, and
  quotient presentation `TauCeti.MappingTelescope.isQuotientMap_sigma_mkCyl`.
* `TauCeti.MappingTelescope.lift`: the universal property out of the mapping telescope, accompanied
  by `TauCeti.MappingTelescope.hom_ext`, `TauCeti.MappingTelescope.ind`, and the product continuity
  criterion `TauCeti.MappingTelescope.continuous_prod_iff`.
* `TauCeti.MappingTelescope.isClosedEmbedding_incl` and
  `TauCeti.MappingTelescope.isClosedEmbedding_fromMappingCylinder`: closed embeddings of each stage
  and of each individual mapping cylinder into the telescope.
* `TauCeti.MappingTelescope.bondOfLE`, `TauCeti.MappingTelescope.inclHomotopy`, and
  `TauCeti.MappingTelescope.inclHomotopyOfLE`: composite bonding maps and canonical homotopies
  relating stage inclusions.
* `T1Space`, `T2Space`, and `UCompactlyGeneratedSpace` instances on `TauCeti.MappingTelescope f`.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.F and Appendix, Proposition A.11.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 14.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

universe u v w

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]

/-- Normal form on `Σ n, I × X n` for the mapping telescope of `f`: a point `(1, x)` on the top
face of the `n`-th cylinder is sent to `(0, f n x)` on the bottom face of the `(n + 1)`-st
cylinder, and every point of height different from `1` is fixed. Because `0 ≠ 1` in `I`, this map
is idempotent and two points have the same normal form precisely when the telescope gluing
identifies them. -/
private def telescopeNormalize (f : ∀ n, C(X n, X (n + 1))) (a : Σ n, I × X n) : Σ n, I × X n :=
  if a.2.1 = 1 then ⟨a.1 + 1, (0, f a.1 a.2.2)⟩ else a

/-- The **mapping telescope** of a sequence of continuous maps `f : ∀ n, C(X n, X (n + 1))`: the
disjoint union of cylinders `Σ n, I × X n` with `(1, x)` in `I × X n` identified with
`(0, f n x)` in `I × X (n + 1)`.

The quotient presentation is private to this file; callers construct points via
`TauCeti.MappingTelescope.mkCyl` and `TauCeti.MappingTelescope.incl`, eliminate via
`TauCeti.MappingTelescope.lift` and `TauCeti.MappingTelescope.ind`, and prove map equality via
`TauCeti.MappingTelescope.hom_ext`. -/
def MappingTelescope (f : ∀ n, C(X n, X (n + 1))) : Type u :=
  Quotient (Setoid.ker (telescopeNormalize f))

namespace MappingTelescope

variable {f : ∀ n, C(X n, X (n + 1))}

@[no_expose] instance : TopologicalSpace (MappingTelescope f) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.ker (telescopeNormalize f))))

/-- The map sending a point of the `n`-th cylinder `I × X n` to its class in the mapping
telescope. -/
def mkCyl (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : C(I × X n, MappingTelescope f) :=
  ⟨fun p => Quotient.mk _ ⟨n, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The inclusion of the `n`-th space `X n` into the mapping telescope as the bottom face
`{0} × X n` of the `n`-th cylinder. -/
def incl (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : C(X n, MappingTelescope f) :=
  (mkCyl f n).comp ⟨fun x => (0, x), by fun_prop⟩

@[simp]
lemma incl_apply (n : ℕ) (x : X n) : incl f n x = mkCyl f n (0, x) := (rfl)

private lemma mkCyl_eq_mkCyl_iff' {m n : ℕ} {p : I × X m} {q : I × X n} :
    mkCyl f m p = mkCyl f n q ↔ telescopeNormalize f ⟨m, p⟩ = telescopeNormalize f ⟨n, q⟩ :=
  Quotient.eq (r := Setoid.ker (telescopeNormalize f))

/-- The top face `{1} × X n` of the `n`-th cylinder is glued to the bottom face `{0} × X (n + 1)`
of the `(n + 1)`-st cylinder along `f n`. -/
@[simp]
lemma mkCyl_one (n : ℕ) (x : X n) : mkCyl f n (1, x) = mkCyl f (n + 1) (0, f n x) :=
  mkCyl_eq_mkCyl_iff'.2 (by simp [telescopeNormalize])

/-- Complete point-identification criterion in the mapping telescope: two cylinder points agree
if and only if they are identical, both lie on the top face of the same cylinder with the same
image under `f`, or one lies on a top face and the other is its glued image on the next bottom
face. -/
@[simp]
lemma mkCyl_eq_mkCyl_iff {m n : ℕ} {s t : I} {x : X m} {y : X n} :
    mkCyl f m (s, x) = mkCyl f n (t, y) ↔
      (∃ h : m = n, s = t ∧ h ▸ x = y) ∨
      (∃ h : m = n, s = 1 ∧ t = 1 ∧ f n (h ▸ x) = f n y) ∨
      (∃ h : m + 1 = n, s = 1 ∧ t = 0 ∧ h ▸ f m x = y) ∨
      (∃ h : n + 1 = m, s = 0 ∧ t = 1 ∧ x = h ▸ f n y) := by
  rw [mkCyl_eq_mkCyl_iff']
  simp only [telescopeNormalize]
  split_ifs with hs ht ht
  · constructor
    · intro h
      obtain ⟨hm, hxy⟩ := Sigma.mk.inj_iff.1 h
      obtain rfl : m = n := by omega
      simp only [Prod.mk.injEq, true_and, heq_eq_eq] at hxy
      exact Or.inr (Or.inl ⟨rfl, hs, ht, hxy⟩)
    · rintro (⟨rfl, -, rfl⟩ | ⟨rfl, -, -, hxy⟩ | ⟨rfl, -, ht0, -⟩ | ⟨rfl, hs0, -, -⟩)
      · rfl
      · exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl hxy))
      · exact absurd (ht.symm.trans ht0) one_ne_zero
      · exact absurd (hs.symm.trans hs0) one_ne_zero
  · constructor
    · intro h
      obtain ⟨rfl, hxy⟩ := Sigma.mk.inj_iff.1 h
      simp only [heq_eq_eq, Prod.mk.injEq] at hxy
      exact Or.inr (Or.inr (Or.inl ⟨rfl, hs, hxy.1.symm, hxy.2⟩))
    · rintro (⟨rfl, hst, -⟩ | ⟨-, -, ht1, -⟩ | ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, _, ht1, -⟩)
      · exact absurd (hst.symm.trans hs) ht
      · exact absurd ht1 ht
      · rfl
      · exact absurd ht1 ht
  · constructor
    · intro h
      obtain ⟨rfl, hxy⟩ := Sigma.mk.inj_iff.1 h
      simp only [heq_eq_eq, Prod.mk.injEq] at hxy
      exact Or.inr (Or.inr (Or.inr ⟨rfl, hxy.1, ht, hxy.2⟩))
    · rintro (⟨rfl, hst, -⟩ | ⟨-, hs1, -, -⟩ | ⟨rfl, hs1, -, -⟩ | ⟨rfl, rfl, -, rfl⟩)
      · exact absurd (hst.trans ht) hs
      · exact absurd hs1 hs
      · exact absurd hs1 hs
      · rfl
  · constructor
    · intro h
      obtain ⟨rfl, hxy⟩ := Sigma.mk.inj_iff.1 h
      simp only [heq_eq_eq, Prod.mk.injEq] at hxy
      exact Or.inl ⟨rfl, hxy.1, hxy.2⟩
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨-, hs1, -⟩ | ⟨-, hs1, -⟩ | ⟨-, -, ht1, -⟩)
      · rfl
      · exact absurd hs1 hs
      · exact absurd hs1 hs
      · exact absurd ht1 ht

lemma mkCyl_eq_mkCyl_same_iff {n : ℕ} {s t : I} {x y : X n} :
    mkCyl f n (s, x) = mkCyl f n (t, y) ↔
      (s = t ∧ x = y) ∨ (s = 1 ∧ t = 1 ∧ f n x = f n y) := by
  rw [mkCyl_eq_mkCyl_iff]
  constructor
  · rintro (⟨_, hst, hxy⟩ | ⟨_, hs, ht, hxy⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact Or.inl ⟨hst, by simpa using hxy⟩
    · exact Or.inr ⟨hs, ht, by simpa using hxy⟩
    · omega
    · omega
  · rintro (⟨hst, hxy⟩ | ⟨hs, ht, hxy⟩)
    · exact Or.inl ⟨rfl, hst, hxy⟩
    · exact Or.inr (Or.inl ⟨rfl, hs, ht, hxy⟩)

lemma incl_inj {n : ℕ} {x y : X n} : incl f n x = incl f n y ↔ x = y := by
  simp [incl_apply]

lemma incl_injective (n : ℕ) : Function.Injective (incl f n) := fun _ _ => incl_inj.1

lemma incl_eq_incl_iff {m n : ℕ} {x : X m} {y : X n} :
    incl f m x = incl f n y ↔ ∃ h : m = n, h ▸ x = y := by
  simp only [incl_apply, mkCyl_eq_mkCyl_iff, zero_ne_one, false_and, and_false, exists_false,
    or_false, true_and]

/-- Induction principle for points of the mapping telescope. -/
@[elab_as_elim]
lemma ind {p : MappingTelescope f → Prop} (cyl : ∀ (n : ℕ) (q : I × X n), p (mkCyl f n q))
    (z : MappingTelescope f) : p z := by
  induction z using Quotient.ind with
  | _ a => exact cyl a.1 a.2

/-- Every point of the mapping telescope has a representative of height strictly less than `1`. -/
@[elab_as_elim]
lemma ind_ne_one {p : MappingTelescope f → Prop}
    (cyl : ∀ (n : ℕ) (s : I) (x : X n), s ≠ 1 → p (mkCyl f n (s, x)))
    (z : MappingTelescope f) : p z := by
  induction z using ind with
  | cyl n q =>
    obtain ⟨s, x⟩ := q
    by_cases hs : s = 1
    · subst hs
      rw [mkCyl_one]
      exact cyl (n + 1) 0 (f n x) zero_ne_one
    · exact cyl n s x hs

/-- **The mapping telescope is a quotient of `Σ n, I × X n`.** -/
theorem isQuotientMap_sigma_mkCyl :
    IsQuotientMap fun p : Σ n, I × X n => mkCyl f p.1 p.2 :=
  isQuotientMap_quot_mk

/-- A subset of the mapping telescope is open if and only if its preimage in every cylinder is
open. -/
theorem isOpen_iff {U : Set (MappingTelescope f)} :
    IsOpen U ↔ ∀ n, IsOpen (mkCyl f n ⁻¹' U) := by
  rw [← isQuotientMap_sigma_mkCyl.isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- A subset of the mapping telescope is closed if and only if its preimage in every cylinder is
closed. -/
theorem isClosed_iff {S : Set (MappingTelescope f)} :
    IsClosed S ↔ ∀ n, IsClosed (mkCyl f n ⁻¹' S) := by
  rw [← isQuotientMap_sigma_mkCyl.isClosed_preimage, isClosed_sigma_iff]
  rfl

section Lift

variable {W : Type w} [TopologicalSpace W] {g : ∀ n, C(I × X n, W)}

private lemma sigma_telescopeNormalize (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x))
    (a : Σ n, I × X n) :
    (fun b : Σ n, I × X n => g b.1 b.2) (telescopeNormalize f a) = g a.1 a.2 := by
  obtain ⟨n, s, x⟩ := a
  by_cases hs : s = 1
  · subst hs
    have hnorm : telescopeNormalize f ⟨n, (1, x)⟩ = ⟨n + 1, (0, f n x)⟩ := by
      simp [telescopeNormalize]
    rw [hnorm, hg]
  · have hnorm : telescopeNormalize f ⟨n, (s, x)⟩ = ⟨n, (s, x)⟩ := by
      simp [telescopeNormalize, hs]
    rw [hnorm]

/-- **Universal property of the mapping telescope.** A family of continuous maps on the cylinders
`I × X n` that agree along each gluing `g n (1, x) = g (n + 1) (0, f n x)` descends to a continuous
map out of the mapping telescope. -/
def lift (g : ∀ n, C(I × X n, W)) (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x)) :
    C(MappingTelescope f, W) :=
  ⟨Quotient.lift (fun a : Σ n, I × X n => g a.1 a.2) fun a b hab => by
      rw [← sigma_telescopeNormalize hg a, ← sigma_telescopeNormalize hg b, hab],
    Continuous.quotient_lift (continuous_sigma fun n => (g n).continuous) _⟩

@[simp]
lemma lift_mkCyl (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x)) (n : ℕ) (p : I × X n) :
    lift g hg (mkCyl f n p) = g n p := (rfl)

lemma lift_incl (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x)) (n : ℕ) (x : X n) :
    lift g hg (incl f n x) = g n (0, x) := (rfl)

/-- **Extensionality for maps out of the mapping telescope.** -/
@[ext]
theorem hom_ext {F G : C(MappingTelescope f, W)}
    (hcyl : ∀ (n : ℕ) (p : I × X n), F (mkCyl f n p) = G (mkCyl f n p)) : F = G := by
  refine ContinuousMap.ext fun z => ?_
  induction z using ind with
  | cyl n p => exact hcyl n p

/-- **Uniqueness in the universal property of the mapping telescope.** -/
theorem lift_unique (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x)) {F : C(MappingTelescope f, W)}
    (hcyl : ∀ (n : ℕ) (p : I × X n), F (mkCyl f n p) = g n p) : F = lift g hg :=
  hom_ext fun n p => by rw [hcyl, lift_mkCyl]

end Lift

/-- **Continuity criterion for maps out of `Z × MappingTelescope f`.** For a locally compact space
`Z`, a map out of `Z × MappingTelescope f` is continuous if and only if its restriction to each
`Z × (I × X n)` is continuous. Taking `Z = I` builds homotopies on the mapping telescope. -/
theorem continuous_prod_iff {Z W : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    [TopologicalSpace W] {g : Z × MappingTelescope f → W} :
    Continuous g ↔ ∀ n, Continuous fun q : Z × (I × X n) => g (q.1, mkCyl f n q.2) := by
  refine ⟨fun hg n => hg.comp (by fun_prop), fun h =>
    isQuotientMap_sigma_mkCyl.continuous_lift_prod_right ?_⟩
  -- Distribute `Z × Σ n, I × X n` into `Σ n, (I × X n) × Z`.
  rw [← ((Homeomorph.prodComm Z (Σ n, I × X n)).trans
    Homeomorph.sigmaProdDistrib).symm.comp_continuous_iff', continuous_sigma_iff]
  intro n
  exact (h n).comp continuous_swap

section Embeddings

private lemma preimage_mkCyl_image_incl (n m : ℕ) (K : Set (X n)) :
    mkCyl f m ⁻¹' (incl f n '' K) =
      if h : m = n then {p : I × X m | p.1 = 0 ∧ h ▸ p.2 ∈ K}
      else if h' : m + 1 = n then {p : I × X m | p.1 = 1 ∧ h' ▸ f m p.2 ∈ K}
      else ∅ := by
  ext ⟨s, y⟩
  simp only [mem_preimage, mem_image, incl_apply]
  split_ifs with h h'
  · subst h
    rw [mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, heq⟩
      rcases mkCyl_eq_mkCyl_same_iff.1 heq with ⟨rfl, rfl⟩ | ⟨h01, -⟩
      · exact ⟨rfl, hx⟩
      · exact absurd h01 zero_ne_one
    · rintro ⟨rfl, hy⟩
      exact ⟨y, hy, rfl⟩
  · subst h'
    rw [mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, heq⟩
      rcases mkCyl_eq_mkCyl_iff.1 heq with
        ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨_, _, hs1, rfl⟩
      · omega
      · omega
      · omega
      · exact ⟨hs1, hx⟩
    · rintro ⟨rfl, hy⟩
      exact ⟨f m y, hy, (mkCyl_one m y).symm⟩
  · simp only [mem_empty_iff_false, iff_false, not_exists, not_and]
    intro x _ heq
    rcases mkCyl_eq_mkCyl_iff.1 heq with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨_, h01, -⟩ | ⟨rfl, -⟩
    · exact h rfl
    · exact h rfl
    · exact zero_ne_one h01
    · exact h' rfl

/-- **Every stage `X n` embeds as a closed subspace of the mapping telescope.** -/
theorem isClosedEmbedding_incl (n : ℕ) : IsClosedEmbedding (incl f n) := by
  refine .of_continuous_injective_isClosedMap (incl f n).continuous (incl_injective n) fun K hK =>
    isClosed_iff.2 fun m => ?_
  rw [preimage_mkCyl_image_incl]
  split_ifs with h h'
  · subst h
    exact (isClosed_singleton.preimage continuous_fst).inter (hK.preimage continuous_snd)
  · subst h'
    exact (isClosed_singleton.preimage continuous_fst).inter
      (hK.preimage ((f m).continuous.comp continuous_snd))
  · exact isClosed_empty

/-- The image of `X n` in the mapping telescope is closed. -/
theorem isClosed_range_incl (n : ℕ) : IsClosed (Set.range (incl f n)) :=
  (isClosedEmbedding_incl n).isClosed_range

/-- Each stage `X n` is homeomorphic to its image in the mapping telescope. -/
def inclHomeomorph (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : X n ≃ₜ Set.range (incl f n) :=
  (isClosedEmbedding_incl (f := f) n).isEmbedding.toHomeomorph

@[simp]
lemma inclHomeomorph_apply_coe (n : ℕ) (x : X n) :
    (inclHomeomorph f n x : MappingTelescope f) = incl f n x := (rfl)

/-- The canonical map from the individual mapping cylinder `MappingCylinder (f n)` into the
mapping telescope, embedding the `n`-th cylinder and its glued base `X (n + 1)`. -/
def fromMappingCylinder (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) :
    C(MappingCylinder (f n), MappingTelescope f) :=
  MappingCylinder.lift (mkCyl f n) (incl f (n + 1)) fun x => mkCyl_one n x

@[simp]
lemma fromMappingCylinder_mkCyl (n : ℕ) (p : I × X n) :
    fromMappingCylinder f n (MappingCylinder.mkCyl (f n) p) = mkCyl f n p :=
  MappingCylinder.lift_mkCyl _ p

@[simp]
lemma fromMappingCylinder_mkBase (n : ℕ) (y : X (n + 1)) :
    fromMappingCylinder f n (MappingCylinder.mkBase (f n) y) = incl f (n + 1) y :=
  MappingCylinder.lift_mkBase _ y

lemma fromMappingCylinder_incl (n : ℕ) (x : X n) :
    fromMappingCylinder f n (MappingCylinder.incl (f n) x) = incl f n x := by
  rw [MappingCylinder.incl_apply, fromMappingCylinder_mkCyl, incl_apply]

@[simp]
lemma fromMappingCylinder_comp_incl (n : ℕ) :
    (fromMappingCylinder f n).comp (MappingCylinder.incl (f n)) = incl f n :=
  ContinuousMap.ext (fromMappingCylinder_incl n)

@[simp]
lemma fromMappingCylinder_comp_mkBase (n : ℕ) :
    (fromMappingCylinder f n).comp (MappingCylinder.mkBase (f n)) = incl f (n + 1) :=
  ContinuousMap.ext (fromMappingCylinder_mkBase n)

lemma fromMappingCylinder_injective (n : ℕ) : Function.Injective (fromMappingCylinder f n) := by
  intro a b hab
  induction a using MappingCylinder.ind with
  | cyl p =>
    obtain ⟨ps, px⟩ := p
    induction b using MappingCylinder.ind with
    | cyl q =>
      obtain ⟨qs, qx⟩ := q
      rw [fromMappingCylinder_mkCyl, fromMappingCylinder_mkCyl, mkCyl_eq_mkCyl_same_iff] at hab
      exact MappingCylinder.mkCyl_eq_mkCyl_iff.2 hab
    | base y =>
      rw [fromMappingCylinder_mkCyl, fromMappingCylinder_mkBase, incl_apply,
        mkCyl_eq_mkCyl_iff] at hab
      rcases hab with ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, hs, _, rfl⟩ | ⟨h, -⟩
      · omega
      · omega
      · subst hs
        exact MappingCylinder.mkCyl_one px
      · omega
  | base y =>
    induction b using MappingCylinder.ind with
    | cyl q =>
      obtain ⟨qs, qx⟩ := q
      rw [fromMappingCylinder_mkBase, fromMappingCylinder_mkCyl, incl_apply,
        mkCyl_eq_mkCyl_iff] at hab
      rcases hab with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, _, ht, rfl⟩
      · omega
      · omega
      · omega
      · subst ht
        exact (MappingCylinder.mkCyl_one qx).symm
    | base z =>
      rw [fromMappingCylinder_mkBase, fromMappingCylinder_mkBase, incl_inj] at hab
      exact congrArg _ hab

private lemma mem_image_fromMappingCylinder_succ {n : ℕ} {K : Set (MappingCylinder (f n))}
    {s : I} {y : X (n + 1)} :
    mkCyl f (n + 1) (s, y) ∈ fromMappingCylinder f n '' K ↔
      s = 0 ∧ MappingCylinder.mkBase (f n) y ∈ K := by
  simp only [mem_image]
  constructor
  · rintro ⟨w, hwK, hw⟩
    induction w using MappingCylinder.ind with
    | cyl q =>
      obtain ⟨qt, qx⟩ := q
      rw [fromMappingCylinder_mkCyl, mkCyl_eq_mkCyl_iff] at hw
      rcases hw with ⟨h', -⟩ | ⟨h', -⟩ | ⟨_, hq1, hs0, hy⟩ | ⟨h', -⟩
      · omega
      · omega
      · subst hq1 hy
        rw [MappingCylinder.mkCyl_one] at hwK
        exact ⟨hs0, hwK⟩
      · omega
    | base z =>
      rw [fromMappingCylinder_mkBase, incl_apply, mkCyl_eq_mkCyl_same_iff] at hw
      rcases hw with ⟨hs0, hzy⟩ | ⟨h01, -⟩
      · exact ⟨hs0.symm, hzy ▸ hwK⟩
      · exact absurd h01 zero_ne_one
  · rintro ⟨rfl, hyK⟩
    exact ⟨MappingCylinder.mkBase (f n) y, hyK, by simp⟩

private lemma mem_image_fromMappingCylinder_pred {m : ℕ} {K : Set (MappingCylinder (f (m + 1)))}
    {s : I} {y : X m} :
    mkCyl f m (s, y) ∈ fromMappingCylinder f (m + 1) '' K ↔
      s = 1 ∧ MappingCylinder.incl (f (m + 1)) (f m y) ∈ K := by
  simp only [mem_image]
  constructor
  · rintro ⟨w, hwK, hw⟩
    induction w using MappingCylinder.ind with
    | cyl q =>
      obtain ⟨qt, qx⟩ := q
      rw [fromMappingCylinder_mkCyl, mkCyl_eq_mkCyl_iff] at hw
      rcases hw with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨_, hq0, hs1, hq2⟩
      · omega
      · omega
      · omega
      · subst hq0 hq2
        rw [← MappingCylinder.incl_apply] at hwK
        exact ⟨hs1, by simpa using hwK⟩
    | base z =>
      rw [fromMappingCylinder_mkBase, incl_apply, mkCyl_eq_mkCyl_iff] at hw
      rcases hw with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> omega
  · rintro ⟨rfl, hyK⟩
    exact ⟨MappingCylinder.incl (f (m + 1)) (f m y), hyK, by
      rw [fromMappingCylinder_incl, incl_apply, mkCyl_one]⟩

private lemma preimage_mkCyl_image_fromMappingCylinder (n m : ℕ)
    (K : Set (MappingCylinder (f n))) :
    mkCyl f m ⁻¹' (fromMappingCylinder f n '' K) =
      if h : m = n then h ▸ (MappingCylinder.mkCyl (f n) ⁻¹' K)
      else if h1 : m = n + 1 then
        {p : I × X m | p.1 = 0 ∧ MappingCylinder.mkBase (f n) (h1 ▸ p.2) ∈ K}
      else if h0 : m + 1 = n then
        {p : I × X m | p.1 = 1 ∧ MappingCylinder.incl (f n) (h0 ▸ f m p.2) ∈ K}
      else ∅ := by
  ext ⟨s, y⟩
  simp only [mem_preimage]
  split_ifs with h h1 h0
  · subst h
    rw [← fromMappingCylinder_mkCyl m (s, y), (fromMappingCylinder_injective m).mem_set_image]
    rfl
  · subst h1
    exact mem_image_fromMappingCylinder_succ
  · subst h0
    exact mem_image_fromMappingCylinder_pred
  · simp only [mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
    intro w _ hw
    induction w using MappingCylinder.ind with
    | cyl q =>
      obtain ⟨qt, qx⟩ := q
      rw [fromMappingCylinder_mkCyl, mkCyl_eq_mkCyl_iff] at hw
      rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact h rfl
      · exact h rfl
      · exact h1 rfl
      · exact h0 rfl
    | base z =>
      rw [fromMappingCylinder_mkBase, incl_apply, mkCyl_eq_mkCyl_iff] at hw
      rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨_, h01, -⟩ | ⟨h', -⟩
      · exact h1 rfl
      · exact h1 rfl
      · exact zero_ne_one h01
      · omega

/-- **Each individual mapping cylinder `MappingCylinder (f n)` embeds as a closed subspace of the
mapping telescope.** -/
theorem isClosedEmbedding_fromMappingCylinder (n : ℕ) :
    IsClosedEmbedding (fromMappingCylinder f n) := by
  refine .of_continuous_injective_isClosedMap (fromMappingCylinder f n).continuous
    (fromMappingCylinder_injective n) fun K hK => isClosed_iff.2 fun m => ?_
  rw [preimage_mkCyl_image_fromMappingCylinder]
  split_ifs with h h1 h0
  · subst h
    exact hK.preimage (MappingCylinder.mkCyl (f m)).continuous
  · subst h1
    exact (isClosed_singleton.preimage continuous_fst).inter
      (hK.preimage ((MappingCylinder.mkBase (f n)).continuous.comp continuous_snd))
  · subst h0
    exact (isClosed_singleton.preimage continuous_fst).inter
      (hK.preimage ((MappingCylinder.incl (f (m + 1))).continuous.comp
        ((f m).continuous.comp continuous_snd)))
  · exact isClosed_empty

/-- The range of `fromMappingCylinder f n` is the union of the `n`-th cylinder with the `(n + 1)`-st
stage inclusion. -/
theorem range_fromMappingCylinder (n : ℕ) :
    Set.range (fromMappingCylinder f n) = Set.range (mkCyl f n) ∪ Set.range (incl f (n + 1)) := by
  ext z
  simp only [mem_range, mem_union]
  constructor
  · rintro ⟨w, rfl⟩
    induction w using MappingCylinder.ind with
    | cyl p => exact Or.inl ⟨p, (fromMappingCylinder_mkCyl n p).symm⟩
    | base y => exact Or.inr ⟨y, (fromMappingCylinder_mkBase n y).symm⟩
  · rintro (⟨p, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨MappingCylinder.mkCyl (f n) p, fromMappingCylinder_mkCyl n p⟩
    · exact ⟨MappingCylinder.mkBase (f n) y, fromMappingCylinder_mkBase n y⟩

end Embeddings

section SeparationAndCompactGeneration

/-- If every stage `X n` is `T₁`, then so is the mapping telescope. -/
instance [∀ n, T1Space (X n)] : T1Space (MappingTelescope f) where
  t1 z := by
    induction z using ind_ne_one with
    | cyl n s x hs =>
      by_cases hs0 : s = 0
      · subst hs0
        rw [← incl_apply, ← Set.image_singleton]
        exact (isClosedEmbedding_incl n).isClosedMap _ isClosed_singleton
      · refine isClosed_iff.2 fun m => ?_
        by_cases hmn : m = n
        · subst hmn
          have hpre : mkCyl f m ⁻¹' {mkCyl f m (s, x)} = {(s, x)} := by
            ext ⟨t, y⟩
            simp only [mem_preimage, mem_singleton_iff, mkCyl_eq_mkCyl_same_iff, Prod.mk.injEq]
            exact ⟨by rintro (h | ⟨-, ht1, -⟩); exacts [h, absurd ht1 hs], Or.inl⟩
          rw [hpre]
          exact isClosed_singleton
        · have hpre : mkCyl f m ⁻¹' {mkCyl f n (s, x)} = ∅ := by
            ext ⟨t, y⟩
            simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
            intro heq
            rcases mkCyl_eq_mkCyl_iff.1 heq with
              ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨_, -, h0, -⟩ | ⟨_, -, ht1, -⟩
            · exact hmn rfl
            · exact hmn rfl
            · exact hs0 h0
            · exact hs ht1
          rw [hpre]
          exact isClosed_empty

/-- An open subset inside the interior `(0, 1) × X n` of a single cylinder, saturated for the
telescope quotient because it avoids both `0` and `1`. -/
private def interiorCylSet (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) (V : Set I) (U : Set (X n)) :
    Set (MappingTelescope f) :=
  mkCyl f n '' (V ×ˢ U)

private lemma mem_interiorCylSet_iff {n m : ℕ} {V : Set I} {U : Set (X n)}
    (hV0 : (0 : I) ∉ V) (hV1 : (1 : I) ∉ V) {t : I} {y : X m} :
    mkCyl f m (t, y) ∈ interiorCylSet f n V U ↔ ∃ h : m = n, t ∈ V ∧ h ▸ y ∈ U := by
  simp only [interiorCylSet, mem_image, Prod.exists, mem_prod]
  constructor
  · rintro ⟨s, x, ⟨hsV, hxU⟩, heq⟩
    rcases mkCyl_eq_mkCyl_iff.1 heq with
      ⟨rfl, rfl, rfl⟩ | ⟨-, hs1, -⟩ | ⟨-, hs1, -⟩ | ⟨-, hs0, -⟩
    · exact ⟨rfl, hsV, hxU⟩
    · exact absurd (hs1 ▸ hsV) hV1
    · exact absurd (hs1 ▸ hsV) hV1
    · exact absurd (hs0 ▸ hsV) hV0
  · rintro ⟨rfl, htV, hyU⟩
    exact ⟨t, y, ⟨htV, hyU⟩, rfl⟩

private lemma isOpen_interiorCylSet {n : ℕ} {V : Set I} {U : Set (X n)}
    (hV : IsOpen V) (hU : IsOpen U) (hV0 : (0 : I) ∉ V) (hV1 : (1 : I) ∉ V) :
    IsOpen (interiorCylSet f n V U) := by
  refine isOpen_iff.2 fun m => ?_
  by_cases hmn : m = n
  · subst hmn
    have hpre : mkCyl f m ⁻¹' interiorCylSet f m V U = V ×ˢ U := by
      ext ⟨t, y⟩
      rw [mem_preimage, mem_interiorCylSet_iff hV0 hV1, mem_prod]
      exact ⟨by rintro ⟨_, ht, hy⟩; exact ⟨ht, by simpa using hy⟩,
        fun ⟨ht, hy⟩ => ⟨rfl, ht, hy⟩⟩
    rw [hpre]
    exact hV.prod hU
  · convert isOpen_empty using 1
    ext ⟨t, y⟩
    simp [mem_interiorCylSet_iff (f := f) hV0 hV1, hmn]

/-- An open collar neighbourhood around `{0} × U` at stage `n`, extending by `< ε` into cylinder
`n` and by `> 1 - ε` into cylinder `n - 1` along `(f (n - 1))⁻¹(U)`. -/
private def seamSet (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) (ε : ℝ) (U : Set (X n)) :
    Set (MappingTelescope f) :=
  mkCyl f n '' ({t : I | (t : ℝ) < ε} ×ˢ U) ∪
    {z | ∃ (m : ℕ) (hm : m + 1 = n) (t : I) (y : X m),
      1 - ε < (t : ℝ) ∧ hm ▸ f m y ∈ U ∧ z = mkCyl f m (t, y)}

private lemma mem_seamSet_same {n : ℕ} {ε : ℝ} (hε1 : ε < 1) {U : Set (X n)} {s : I} {y : X n} :
    mkCyl f n (s, y) ∈ seamSet f n ε U ↔ (s : ℝ) < ε ∧ y ∈ U := by
  simp only [seamSet, mem_union, mem_image, Prod.exists, mem_prod, mem_ofPred_eq]
  constructor
  · rintro (⟨t, x, ⟨ht, hx⟩, heq⟩ | ⟨k, hk, t, x, ht, hx, heq⟩)
    · rcases mkCyl_eq_mkCyl_same_iff.1 heq.symm with ⟨rfl, rfl⟩ | ⟨_, ht1, -⟩
      · exact ⟨ht, hx⟩
      · subst ht1
        rw [Set.Icc.coe_one] at ht
        linarith
    · subst hk
      rcases mkCyl_eq_mkCyl_iff.1 heq with
        ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨_, hs0, _, rfl⟩
      · omega
      · omega
      · omega
      · subst hs0
        exact ⟨by rw [Set.Icc.coe_zero]; linarith [t.2.2], hx⟩
  · rintro ⟨hs, hy⟩
    exact Or.inl ⟨s, y, ⟨hs, hy⟩, rfl⟩

private lemma mem_seamSet_pred {m : ℕ} {ε : ℝ} {U : Set (X (m + 1))} {s : I} {y : X m} :
    mkCyl f m (s, y) ∈ seamSet f (m + 1) ε U ↔ 1 - ε < (s : ℝ) ∧ f m y ∈ U := by
  simp only [seamSet, mem_union, mem_image, Prod.exists, mem_prod, mem_ofPred_eq]
  constructor
  · rintro (⟨t, x, ⟨ht, hx⟩, heq⟩ | ⟨k, hk, t, x, ht, hx, heq⟩)
    · rcases mkCyl_eq_mkCyl_iff.1 heq with
        ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨_, ht0, hs1, rfl⟩
      · omega
      · omega
      · omega
      · subst ht0 hs1
        rw [Set.Icc.coe_zero] at ht
        exact ⟨by rw [Set.Icc.coe_one]; linarith, hx⟩
    · obtain rfl : k = m := by omega
      rcases mkCyl_eq_mkCyl_same_iff.1 heq with ⟨rfl, rfl⟩ | ⟨ht1, hs1, hfy⟩
      · exact ⟨ht, hx⟩
      · subst ht1 hs1
        exact ⟨ht, hfy ▸ hx⟩
  · rintro ⟨hs, hy⟩
    exact Or.inr ⟨m, rfl, s, y, hs, hy, rfl⟩

private lemma preimage_mkCyl_seamSet {n m : ℕ} {ε : ℝ} (hε1 : ε < 1) (U : Set (X n)) :
    mkCyl f m ⁻¹' seamSet f n ε U =
      if h : m = n then {p : I × X m | (p.1 : ℝ) < ε ∧ h ▸ p.2 ∈ U}
      else if h' : m + 1 = n then {p : I × X m | 1 - ε < (p.1 : ℝ) ∧ h' ▸ f m p.2 ∈ U}
      else ∅ := by
  ext ⟨s, y⟩
  simp only [mem_preimage]
  split_ifs with h h'
  · subst h
    exact mem_seamSet_same hε1
  · subst h'
    exact mem_seamSet_pred
  · simp only [seamSet, mem_union, mem_image, Prod.exists, mem_prod, mem_ofPred_eq,
      mem_empty_iff_false, iff_false]
    rintro (⟨t, x, ⟨ht, _⟩, heq⟩ | ⟨k, hk, t, x, ht, _, heq⟩)
    · rcases mkCyl_eq_mkCyl_iff.1 heq with
        ⟨hnm, -⟩ | ⟨hnm, -⟩ | ⟨_, ht1, -⟩ | ⟨hm1n, -⟩
      · exact h hnm.symm
      · exact h hnm.symm
      · subst ht1
        rw [Set.Icc.coe_one] at ht
        linarith
      · exact h' hm1n
    · subst hk
      rcases mkCyl_eq_mkCyl_iff.1 heq with
        ⟨hmk, -⟩ | ⟨hmk, -⟩ | ⟨_, _, ht0, -⟩ | ⟨hk1m, -⟩
      · exact h' (congrArg (· + 1) hmk)
      · exact h' (congrArg (· + 1) hmk)
      · subst ht0
        rw [Set.Icc.coe_zero] at ht
        linarith
      · exact h hk1m.symm

private lemma isOpen_seamSet {n : ℕ} {ε : ℝ} (hε1 : ε < 1) {U : Set (X n)} (hU : IsOpen U) :
    IsOpen (seamSet f n ε U) := by
  refine isOpen_iff.2 fun m => ?_
  rw [preimage_mkCyl_seamSet hε1]
  split_ifs with h h'
  · subst h
    exact (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
      (hU.preimage continuous_snd)
  · subst h'
    exact (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).inter
      (hU.preimage ((f m).continuous.comp continuous_snd))
  · exact isOpen_empty

private lemma exists_disjoint_interiorCylSet {n₁ n₂ : ℕ} [T2Space (X n₁)] {t₁ t₂ : I}
    {x₁ : X n₁} {x₂ : X n₂} (hmem₁ : t₁ ∈ Set.Ioo (0 : I) 1) (hmem₂ : t₂ ∈ Set.Ioo (0 : I) 1)
    (hne : mkCyl f n₁ (t₁, x₁) ≠ mkCyl f n₂ (t₂, x₂)) :
    ∃ (V₁ : Set I) (U₁ : Set (X n₁)) (V₂ : Set I) (U₂ : Set (X n₂)),
      IsOpen (interiorCylSet f n₁ V₁ U₁) ∧ IsOpen (interiorCylSet f n₂ V₂ U₂) ∧
      mkCyl f n₁ (t₁, x₁) ∈ interiorCylSet f n₁ V₁ U₁ ∧
      mkCyl f n₂ (t₂, x₂) ∈ interiorCylSet f n₂ V₂ U₂ ∧
      Disjoint (interiorCylSet f n₁ V₁ U₁) (interiorCylSet f n₂ V₂ U₂) := by
  have hIoo : IsOpen (Set.Ioo (0 : I) 1) := isOpen_Ioo
  by_cases hn : n₁ = n₂
  · subst hn
    have hpx : (t₁, x₁) ≠ (t₂, x₂) := fun h => hne (congrArg _ h)
    obtain ⟨W₁, W₂, hW₁, hW₂, hp₁, hp₂, hdisj⟩ := t2_separation hpx
    rcases isOpen_prod_iff.1 hW₁ t₁ x₁ hp₁ with ⟨V₁, U₁, hV₁, hU₁, htV₁, hxU₁, hsub₁⟩
    rcases isOpen_prod_iff.1 hW₂ t₂ x₂ hp₂ with ⟨V₂, U₂, hV₂, hU₂, htV₂, hxU₂, hsub₂⟩
    refine ⟨V₁ ∩ Set.Ioo 0 1, U₁, V₂ ∩ Set.Ioo 0 1, U₂,
      isOpen_interiorCylSet (hV₁.inter hIoo) hU₁ (by simp) (by simp),
      isOpen_interiorCylSet (hV₂.inter hIoo) hU₂ (by simp) (by simp),
      ⟨(t₁, x₁), ⟨⟨htV₁, hmem₁⟩, hxU₁⟩, rfl⟩,
      ⟨(t₂, x₂), ⟨⟨htV₂, hmem₂⟩, hxU₂⟩, rfl⟩,
      Set.disjoint_left.2 fun z hz₁ hz₂ => ?_⟩
    induction z using ind with
    | cyl m q =>
      obtain ⟨rfl, hq₁, hqU₁⟩ := (mem_interiorCylSet_iff (by simp) (by simp)).1 hz₁
      obtain ⟨_, hq₂, hqU₂⟩ := (mem_interiorCylSet_iff (by simp) (by simp)).1 hz₂
      exact Set.disjoint_left.1 hdisj (hsub₁ ⟨hq₁.1, hqU₁⟩) (hsub₂ ⟨hq₂.1, hqU₂⟩)
  · refine ⟨Set.Ioo 0 1, Set.univ, Set.Ioo 0 1, Set.univ,
      isOpen_interiorCylSet hIoo isOpen_univ (by simp) (by simp),
      isOpen_interiorCylSet hIoo isOpen_univ (by simp) (by simp),
      ⟨(t₁, x₁), ⟨hmem₁, trivial⟩, rfl⟩,
      ⟨(t₂, x₂), ⟨hmem₂, trivial⟩, rfl⟩,
      Set.disjoint_left.2 fun z hz₁ hz₂ => ?_⟩
    induction z using ind with
    | cyl m q =>
      obtain ⟨rfl, -⟩ := (mem_interiorCylSet_iff (by simp) (by simp)).1 hz₁
      obtain ⟨rfl, -⟩ := (mem_interiorCylSet_iff (by simp) (by simp)).1 hz₂
      exact hn rfl

private lemma t2_sep_zero_pos {n₁ n₂ : ℕ} {t₂ : I} (x₁ : X n₁) (x₂ : X n₂)
    (ht₂ : t₂ ≠ 0) (ht₂' : t₂ ≠ 1) :
    ∃ U₁ U₂ : Set (MappingTelescope f), IsOpen U₁ ∧ IsOpen U₂ ∧
      mkCyl f n₁ (0, x₁) ∈ U₁ ∧ mkCyl f n₂ (t₂, x₂) ∈ U₂ ∧ Disjoint U₁ U₂ := by
  have ht0 : (0 : ℝ) < t₂ := lt_of_le_of_ne t₂.2.1 (Subtype.coe_ne_coe.2 ht₂.symm)
  have ht1 : (t₂ : ℝ) < 1 := lt_of_le_of_ne t₂.2.2 (Subtype.coe_ne_coe.2 ht₂')
  let ε : ℝ := min (t₂ : ℝ) (1 - t₂) / 2
  have hε_eq : ε = min (t₂ : ℝ) (1 - t₂) / 2 := rfl
  have hε0 : 0 < ε := by positivity
  have hε_lt_t : ε < t₂ := by
    have : min (t₂ : ℝ) (1 - t₂) ≤ t₂ := min_le_left _ _
    linarith
  have ht_lt_one_sub : (t₂ : ℝ) < 1 - ε := by
    have : min (t₂ : ℝ) (1 - t₂) ≤ 1 - t₂ := min_le_right _ _
    linarith
  have hε1 : ε < 1 := by linarith
  let V : Set I := {t : I | ε < (t : ℝ) ∧ (t : ℝ) < 1 - ε}
  have hV : IsOpen V := (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)
  have hV0 : (0 : I) ∉ V := by
    rintro ⟨h, -⟩
    rw [Set.Icc.coe_zero] at h
    linarith
  have hV1 : (1 : I) ∉ V := by
    rintro ⟨-, h⟩
    rw [Set.Icc.coe_one] at h
    linarith
  refine ⟨seamSet f n₁ ε Set.univ, interiorCylSet f n₂ V Set.univ,
    isOpen_seamSet hε1 isOpen_univ, isOpen_interiorCylSet hV isOpen_univ hV0 hV1,
    Or.inl ⟨(0, x₁), ⟨by simp [hε0], trivial⟩, rfl⟩,
    ⟨(t₂, x₂), ⟨⟨hε_lt_t, ht_lt_one_sub⟩, trivial⟩, rfl⟩,
    Set.disjoint_left.2 fun z hz₁ hz₂ => ?_⟩
  induction z using ind with
  | cyl m q =>
    obtain ⟨rfl, ⟨hqε, hq1⟩, -⟩ := (mem_interiorCylSet_iff hV0 hV1).1 hz₂
    have hpre := preimage_mkCyl_seamSet (f := f) (n := n₁) (m := m) hε1 Set.univ
    have hzm : q ∈ mkCyl f m ⁻¹' seamSet f n₁ ε Set.univ := hz₁
    rw [hpre] at hzm
    split_ifs at hzm with hm hm'
    · linarith [hzm.1]
    · linarith [hzm.1]
    · exact hzm

private lemma t2_sep_zero_zero {n₁ n₂ : ℕ} [T2Space (X n₁)] {x₁ : X n₁} {x₂ : X n₂}
    (hne : mkCyl f n₁ (0, x₁) ≠ mkCyl f n₂ (0, x₂)) :
    ∃ U₁ U₂ : Set (MappingTelescope f), IsOpen U₁ ∧ IsOpen U₂ ∧
      mkCyl f n₁ (0, x₁) ∈ U₁ ∧ mkCyl f n₂ (0, x₂) ∈ U₂ ∧ Disjoint U₁ U₂ := by
  have hhalf1 : (1 / 2 : ℝ) < 1 := by norm_num
  by_cases hn : n₁ = n₂
  · subst hn
    have hx : x₁ ≠ x₂ := fun h => hne (congrArg _ (Prod.ext rfl h))
    obtain ⟨U₁, U₂, hU₁, hU₂, hx₁, hx₂, hdisj⟩ := t2_separation hx
    refine ⟨seamSet f n₁ (1 / 2) U₁, seamSet f n₁ (1 / 2) U₂,
      isOpen_seamSet hhalf1 hU₁, isOpen_seamSet hhalf1 hU₂,
      Or.inl ⟨(0, x₁), ⟨by simp, hx₁⟩, rfl⟩,
      Or.inl ⟨(0, x₂), ⟨by simp, hx₂⟩, rfl⟩,
      Set.disjoint_left.2 fun z hz₁ hz₂ => ?_⟩
    induction z using ind with
    | cyl m q =>
      have h₁ : q ∈ mkCyl f m ⁻¹' seamSet f n₁ (1 / 2) U₁ := hz₁
      have h₂ : q ∈ mkCyl f m ⁻¹' seamSet f n₁ (1 / 2) U₂ := hz₂
      rw [preimage_mkCyl_seamSet hhalf1] at h₁ h₂
      split_ifs at h₁ h₂ with hm hm'
      · subst hm
        exact Set.disjoint_left.1 hdisj h₁.2 h₂.2
      · subst hm'
        exact Set.disjoint_left.1 hdisj h₁.2 h₂.2
      · exact h₁
  · refine ⟨seamSet f n₁ (1 / 2) Set.univ, seamSet f n₂ (1 / 2) Set.univ,
      isOpen_seamSet hhalf1 isOpen_univ,
      isOpen_seamSet hhalf1 isOpen_univ,
      Or.inl ⟨(0, x₁), ⟨by simp, trivial⟩, rfl⟩,
      Or.inl ⟨(0, x₂), ⟨by simp, trivial⟩, rfl⟩,
      Set.disjoint_left.2 fun z hz₁ hz₂ => ?_⟩
    induction z using ind with
    | cyl m q =>
      have h₁ : q ∈ mkCyl f m ⁻¹' seamSet f n₁ (1 / 2) Set.univ := hz₁
      have h₂ : q ∈ mkCyl f m ⁻¹' seamSet f n₂ (1 / 2) Set.univ := hz₂
      rw [preimage_mkCyl_seamSet hhalf1] at h₁ h₂
      split_ifs at h₁ with hm₁ hm₁' <;> split_ifs at h₂ with hm₂ hm₂'
      · exact hn (hm₁.symm.trans hm₂)
      · linarith [h₁.1, h₂.1]
      · exact h₂
      · linarith [h₁.1, h₂.1]
      · exact hn (hm₁'.symm.trans hm₂')
      · exact h₂
      · exact h₁
      · exact h₁
      · exact h₁

/-- **If every stage `X n` is Hausdorff, then so is the mapping telescope.** -/
instance [∀ n, T2Space (X n)] : T2Space (MappingTelescope f) where
  t2 z₁ z₂ hne := by
    induction z₁ using ind_ne_one with
    | cyl n₁ t₁ x₁ ht₁' =>
      induction z₂ using ind_ne_one with
      | cyl n₂ t₂ x₂ ht₂' =>
        by_cases ht₁ : t₁ = 0
        · subst ht₁
          by_cases ht₂ : t₂ = 0
          · subst ht₂
            exact t2_sep_zero_zero hne
          · exact t2_sep_zero_pos x₁ x₂ ht₂ ht₂'
        · by_cases ht₂ : t₂ = 0
          · subst ht₂
            obtain ⟨U₂, U₁, hU₂, hU₁, hz₂, hz₁, hdisj⟩ := t2_sep_zero_pos x₂ x₁ ht₁ ht₁'
            exact ⟨U₁, U₂, hU₁, hU₂, hz₁, hz₂, hdisj.symm⟩
          · obtain ⟨V₁, U₁, V₂, U₂, hO₁, hO₂, hz₁, hz₂, hd⟩ :=
              exists_disjoint_interiorCylSet
                ⟨lt_of_le_of_ne t₁.2.1 (Ne.symm ht₁), lt_of_le_of_ne t₁.2.2 ht₁'⟩
                ⟨lt_of_le_of_ne t₂.2.1 (Ne.symm ht₂), lt_of_le_of_ne t₂.2.2 ht₂'⟩ hne
            exact ⟨_, _, hO₁, hO₂, hz₁, hz₂, hd⟩

/-- **If every stage `X n` is compactly generated, then so is the mapping telescope.** Since
`CompactlyGeneratedSpace` abbreviates `UCompactlyGeneratedSpace.{u}`, this covers both
`CompactlyGeneratedSpace` and universe-explicit `UCompactlyGeneratedSpace`. -/
instance [∀ n, UCompactlyGeneratedSpace.{v} (X n)] :
    UCompactlyGeneratedSpace.{v} (MappingTelescope f) := by
  refine uCompactlyGeneratedSpace_of_continuous_maps fun {W} _ g hg => ?_
  rw [isQuotientMap_sigma_mkCyl.continuous_iff, continuous_sigma_iff]
  intro n
  have hslice (x : X n) : Continuous fun t : I => g (mkCyl f n (t, x)) := by
    let k₀ : C(ULift.{v} I, MappingTelescope f) := ⟨fun s => mkCyl f n (s.down, x), by fun_prop⟩
    exact (hg (CompHaus.of (ULift.{v} I)) k₀).comp continuous_uliftUp
  let G : X n → C(I, W) := fun x => ⟨fun t => g (mkCyl f n (t, x)), hslice x⟩
  have hG : Continuous G := by
    refine continuous_from_uCompactlyGeneratedSpace G fun S h => ?_
    let k' : C(S × ULift.{v} I, MappingTelescope f) :=
      ⟨fun p => mkCyl f n (p.2.down, h p.1), by fun_prop⟩
    have hc : Continuous fun p : S × I => g (mkCyl f n (p.2, h p.1)) :=
      (hg (CompHaus.of (S × ULift.{v} I)) k').comp
        (continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd))
    exact (ContinuousMap.curry ⟨fun p : S × I => g (mkCyl f n (p.2, h p.1)), hc⟩).continuous
  exact continuous_eval.comp ((hG.comp continuous_snd).prodMk continuous_fst)

end SeparationAndCompactGeneration

section BondingAndHomotopies

/-- The composite bonding map `X m → X n` along `f` for `m ≤ n`. -/
def bondOfLE (f : ∀ n, C(X n, X (n + 1))) : ∀ {m n : ℕ}, m ≤ n → C(X m, X n)
  | m, 0, h => Nat.eq_zero_of_le_zero h ▸ ContinuousMap.id (X m)
  | m, k + 1, h =>
    if hmn : m = k + 1 then hmn ▸ ContinuousMap.id (X m)
    else (f k).comp (bondOfLE f (Nat.le_of_lt_succ (lt_of_le_of_ne h hmn)))

@[simp]
theorem bondOfLE_refl (m : ℕ) : bondOfLE f (le_refl m) = ContinuousMap.id (X m) := by
  cases m <;> simp [bondOfLE]

theorem bondOfLE_step {m k : ℕ} (h : m ≤ k) :
    bondOfLE f (Nat.le_succ_of_le h) = (f k).comp (bondOfLE f h) := by
  have hne : m ≠ k + 1 := by omega
  simp [bondOfLE, hne]

@[simp]
theorem bondOfLE_succ (m : ℕ) : bondOfLE f m.le_succ = f m := by
  rw [bondOfLE_step (le_refl m), bondOfLE_refl, ContinuousMap.comp_id]

@[simp]
theorem bondOfLE_comp_bondOfLE {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (bondOfLE f hmn).comp (bondOfLE f hkm) = bondOfLE f (hkm.trans hmn) := by
  induction n, hmn using Nat.le_induction with
  | base => rw [bondOfLE_refl, ContinuousMap.id_comp]
  | succ n hmn ih =>
    rw [bondOfLE_step hmn, bondOfLE_step (hkm.trans hmn), ContinuousMap.comp_assoc, ih]

@[simp]
theorem bondOfLE_apply_bondOfLE {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (x : X k) :
    bondOfLE f hmn (bondOfLE f hkm x) = bondOfLE f (hkm.trans hmn) x :=
  ContinuousMap.congr_fun (bondOfLE_comp_bondOfLE hkm hmn) x

/-- The canonical homotopy from `incl f n` to `(incl f (n + 1)).comp (f n)` traced out by the `n`-th
cylinder of the mapping telescope. -/
def inclHomotopy (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) :
    (incl f n).Homotopy ((incl f (n + 1)).comp (f n)) where
  toContinuousMap := mkCyl f n
  map_zero_left _ := rfl
  map_one_left x := mkCyl_one n x

@[simp]
lemma inclHomotopy_apply (n : ℕ) (t : I) (x : X n) :
    inclHomotopy f n (t, x) = mkCyl f n (t, x) := (rfl)

/-- The canonical homotopy from `incl f m` to `(incl f n).comp (bondOfLE f h)` for `m ≤ n`,
obtained by concatenating the cylinder homotopies from stage `m` up to stage `n`. -/
def inclHomotopyOfLE (f : ∀ n, C(X n, X (n + 1))) :
    ∀ {m n : ℕ} (h : m ≤ n), (incl f m).Homotopy ((incl f n).comp (bondOfLE f h))
  | m, 0, h =>
    match m, Nat.eq_zero_of_le_zero h with
    | 0, rfl =>
      (ContinuousMap.Homotopy.refl (incl f 0)).cast rfl
        (by rw [bondOfLE_refl, ContinuousMap.comp_id])
  | m, k + 1, h =>
    if hmn : m = k + 1 then
      match m, hmn with
      | _, rfl =>
        (ContinuousMap.Homotopy.refl (incl f (k + 1))).cast rfl
          (by rw [bondOfLE_refl, ContinuousMap.comp_id])
    else
      let hk' : m ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne h hmn)
      ((inclHomotopyOfLE f hk').trans
        ((inclHomotopy f k).compContinuousMap (bondOfLE f hk'))).cast rfl
        (by rw [bondOfLE_step hk', ContinuousMap.comp_assoc])

@[simp]
lemma inclHomotopyOfLE_refl (m : ℕ) :
    inclHomotopyOfLE f (le_refl m) =
      (ContinuousMap.Homotopy.refl (incl f m)).cast rfl
        (by rw [bondOfLE_refl, ContinuousMap.comp_id]) := by
  cases m <;> simp [inclHomotopyOfLE]

lemma inclHomotopyOfLE_step {m k : ℕ} (h : m ≤ k) :
    inclHomotopyOfLE f (Nat.le_succ_of_le h) =
      ((inclHomotopyOfLE f h).trans
        ((inclHomotopy f k).compContinuousMap (bondOfLE f h))).cast rfl
        (by rw [bondOfLE_step h, ContinuousMap.comp_assoc]) := by
  have hne : m ≠ k + 1 := by omega
  simp [inclHomotopyOfLE, hne]

/-- The `m`-th stage inclusion is homotopic to `bondOfLE f h` followed by the `n`-th stage
inclusion. -/
theorem incl_homotopic_comp_bondOfLE {m n : ℕ} (h : m ≤ n) :
    (incl f m).Homotopic ((incl f n).comp (bondOfLE f h)) :=
  ⟨inclHomotopyOfLE f h⟩

/-- Every point `incl f m x` is joined by a path in the mapping telescope to
`incl f n (bondOfLE f h x)`. -/
theorem joined_incl_bondOfLE {m n : ℕ} (h : m ≤ n) (x : X m) :
    Joined (incl f m x) (incl f n (bondOfLE f h x)) :=
  ⟨(inclHomotopyOfLE f h).evalAt x⟩

/-- The canonical real-valued height function on `MappingTelescope f`, sending `mkCyl f n (s, x)`
to `(n : ℝ) + s`. -/
def height (f : ∀ n, C(X n, X (n + 1))) : C(MappingTelescope f, ℝ) :=
  lift (fun n => ⟨fun p => (n : ℝ) + (p.1 : ℝ), continuous_const.add
    (continuous_subtype_val.comp continuous_fst)⟩) fun n _ => by
      simp [add_assoc]

@[simp]
theorem height_mkCyl (n : ℕ) (p : I × X n) :
    height f (mkCyl f n p) = (n : ℝ) + (p.1 : ℝ) :=
  lift_mkCyl _ n p

theorem height_incl (n : ℕ) (x : X n) : height f (incl f n x) = n := by
  simp [incl_apply]

end BondingAndHomotopies

end MappingTelescope

end TauCeti
